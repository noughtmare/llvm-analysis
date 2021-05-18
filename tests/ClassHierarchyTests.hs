module Main ( main ) where

import Data.Generics.Uniplate.Data
import Data.List ( find )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )

import qualified ABI.Itanium as ABI

import LLVM.Analysis
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.Util.Names
import LLVM.Analysis.Util.Testing

import Data.LLVM.BitCode (parseBitCode)
import Text.LLVM.Resolve (resolve)
import qualified Data.ByteString as B
import Data.Either (fromRight)
import LLVM.Types

main :: IO ()
main = do
  args <- getArgs
  let pattern1 = case args of
        [] -> "tests/class-hierarchy/*.cpp"
        [infile] -> infile
        _ -> error "Only one argument allowed"
      pattern2 = case args of
        [] -> "tests/virtual-dispatch/*.cpp"
        [infile] -> infile
        _ -> error "Only one argument allowed"
      testDescriptors = [ TestDescriptor { testPattern = pattern1
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeHierarchy
                                         , testResultComparator = assertEqual
                                         }
                        , TestDescriptor { testPattern = pattern2
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = findCallees
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected opts parser testDescriptors
  where
    opts = [ "-mem2reg", "-basicaa", "-gvn" ]
    parser n h = do
      bc <- B.hGetContents h
      m <- fromRight (error "Parse error") <$> parseBitCode bc
      return (resolve m)


analyzeHierarchy :: Module -> Map String (Set String)
analyzeHierarchy = classHierarchyToTestFormat . runCHA

findCallees :: Module -> Map String (Set String)
findCallees m = M.fromList $ mapMaybe (firstCalleeTargets cha) funcs
  where
    cha = runCHA m
    funcs = modDefines m

defToDemangledName :: Define -> String
defToDemangledName f =
  case parseFunctionName f of
    Left e -> error e
    Right sname ->
      case unparseFunctionName sname of
        Nothing -> error ("Unable to unparse function name: " ++ show sname)
        Just n -> n

firstCalleeTargets :: CHA -> Define -> Maybe (String, Set String)
firstCalleeTargets cha f
  | isConstructor f || isVirtualThunk f = Nothing
  | otherwise = do
      firstCall <- find isCall instrs
      callees <- resolveVirtualCallee cha firstCall
      return (fname, S.fromList (map defToDemangledName callees))
  where
    instrs = map stmtInstr (defStmts f)
    fname = defToDemangledName f

isVirtualThunk :: Define -> Bool
isVirtualThunk f =
  case dname of
    Right (ABI.OverrideThunk _ _) -> True
    Right (ABI.OverrideThunkCovariant _ _ _) -> True
    _ -> False
  where
    n = (\(Symbol n) -> n) (defName f)
    dname = ABI.demangleName n

isConstructor :: Define -> Bool
isConstructor f =
  case dname of
    Left _ -> False
    Right structuredName ->
      case universeBi structuredName of
        [ABI.C2] -> True
        [ABI.C1] -> True
        [ABI.C3] -> True
        _ -> False
  where
    n = (\(Symbol n) -> n) (defName f)
    dname = ABI.demangleName n

isCall :: Instr -> Bool
isCall i =
  case i of
    Call {} -> True
    _ -> False
