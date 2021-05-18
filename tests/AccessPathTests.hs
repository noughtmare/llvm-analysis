module Main ( main ) where

import Data.List ( find )
import Data.Map ( Map )
import qualified Data.Map as M
import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.Util.Testing

import Data.LLVM.BitCode (parseBitCode)
import Text.LLVM.Resolve (resolve)
import qualified Data.ByteString as B
import Data.Either (fromRight)
import LLVM.Types

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/accesspath/*.c"
        [infile] -> infile
        _ -> error "Only one argument allowed"
      testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = extractFirstPath
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected opts parser testDescriptors
  where
    opts = [ "-mem2reg", "-basicaa", "-gvn" ]
    parser n h = do
      bc <- B.hGetContents h
      m <- fromRight (error "Parse error") <$> parseBitCode bc
      -- print m
      return (resolve m)


type Summary = (String, [AccessType])

-- Feed the first store instruction in each function to accessPath and
-- map each function to its path.
extractFirstPath :: Module -> Map String Summary
extractFirstPath m = M.fromList $ map extractFirstFuncPath (modDefines m)

extractFirstFuncPath :: Define -> (String, Summary)
extractFirstFuncPath f = (prettySymbol (defName f), summ)
  where
    allStmts = concatMap bbStmts (defBody f)
    Just firstStore = find (isStore . stmtInstr) allStmts
    Just p = accessPath firstStore
    p' = abstractAccessPath p
    summ = (prettyType (abstractAccessPathBaseType p'),
            abstractAccessPathComponents p')

isStore :: Instr -> Bool
isStore Store {} = True
isStore _ = False
