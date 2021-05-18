{-# LANGUAGE CPP #-}
module Main ( main ) where

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S
import System.Environment ( getArgs, withArgs )
import System.FilePath
import Test.HUnit ( assertEqual )

import LLVM.Analysis
-- import LLVM.Analysis.PointsTo.AllocatorProfile
import LLVM.Analysis.PointsTo.Andersen
import LLVM.Analysis.PointsTo
import LLVM.Analysis.Util.Testing

import Data.LLVM.BitCode (parseBitCode)
import Text.LLVM.Resolve (resolve)
import qualified Data.ByteString as B
import Data.Either (fromRight)
import Data.Maybe (fromMaybe)

import Debug.Trace
import System.IO

#if defined(DEBUGGRAPH)
import Data.GraphViz
import System.IO.Unsafe ( unsafePerformIO )

viewConstraintGraph :: a -> Andersen -> a
viewConstraintGraph v a = unsafePerformIO $ do
  let dg = andersenConstraintGraph a
  runGraphvizCanvas' dg Gtk
  return v
#else
viewConstraintGraph :: a -> Andersen -> a
viewConstraintGraph = const
#endif

-- TODO figure out how to get more sensible value names
extractSummary :: Module -> Map String (Set String)
extractSummary m =
  foldr addInfo mempty ptrs `viewConstraintGraph` pta
  where
    pta = runPointsToAnalysis m
    ptrs = map toValue (globalPointerVariables m) ++ formals -- ++ map Value (functionPointerParameters m)
    formals = concatMap (map toValue . defArgs) (modDefines m)
    addInfo v r
      | null vals = r
      | otherwise = -- trace "!!!HERE!!!" $
          let targets = map (fromMaybe "??" . prettyValName) vals -- `debug` show vals
          in M.insert name (S.fromList targets) r
      where
        vals = {- trace ("pointsTo pta " ++ show (valValue v)) $ -} pointsTo pta v
        name = fromMaybe "???" (valName v) -- TODO figure out why this doesn't need prettyValName

isPointerType :: Type -> Bool
isPointerType t = case t of
  PtrTo _ -> True
  _ -> False

isPointer :: (IsValue a) => a -> Bool
isPointer = isPointerType . valType . toValue

globalPointerVariables :: Module -> [Global]
globalPointerVariables m = filter isPointer (modGlobals m)

functionPointerParameters :: Module -> [Argument]
functionPointerParameters m = concatMap pointerParams (modDefines m)
  where
    pointerParams = filter isPointer . defArgs

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  let pattern = case args of
        [] -> "tests/points-to-inputs/*/*.c"
        [infile] -> infile
        _ -> error "Only one argument allowed"
      testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = expectedMapper
                                         , testResultBuilder = extractSummary
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected opts parser testDescriptors
  where
    -- These optimizations aren't really necessary (the algorithm
    -- works fine with unoptimized bitcode), but comparing the results
    -- visually is much easier with the optimized version.
    opts = [ "-mem2reg", "-basicaa", "-gvn" ]
    expectedMapper = (<.> "expected-andersen")
    parser _ h = do
      bc <- B.hGetContents h
      m <- fromRight (error "Parse error") <$> parseBitCode bc
      -- print m
      let r = resolve m
      -- print r
      return r

