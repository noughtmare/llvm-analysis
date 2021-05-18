module Main ( main ) where

import Data.Functor.Identity
import Data.Foldable ( toList )
import Data.HashSet ( HashSet )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo.TrivialFunction
import LLVM.Analysis.NoReturn
import LLVM.Analysis.Util.Testing
-- import LLVM.Parse

import Data.LLVM.BitCode (parseBitCode)
import Text.LLVM.Resolve (resolve)
import qualified Data.ByteString as B
import Data.Either (fromRight)
import LLVM.Types


main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/noreturn/*.c"
        [infile] -> infile
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeReturns
                                         , testResultComparator = assertEqual
                                         }
                        ]

  withArgs [] $ testAgainstExpected opts parser testDescriptors
  where
    opts = ["-mem2reg", "-basicaa", "-gvn"]
    parser n h = do
      bc <- B.hGetContents h
      m <- fromRight (error "Parse error") <$> parseBitCode bc
      -- print m
      return (resolve m)

exitTest :: Monad m => Declare -> m Bool
exitTest ef = return $ "@exit" == efname
  where
    efname = (\(Symbol s) -> "@" ++ s) (decName ef)

nameToString :: Define -> String
nameToString = (\(Symbol s) -> "@" ++ s) . defName

runNoReturnAnalysis :: CallGraph -> (Declare -> Identity Bool) -> [Define]
runNoReturnAnalysis cg extSummary =
  let analysis :: [CFG] -> HashSet Define -> HashSet Define
      analysis = callGraphAnalysisM runIdentity (noReturnAnalysis extSummary)
      res = callGraphSCCTraversal cg analysis mempty
  in toList res


analyzeReturns :: Module -> Set String
analyzeReturns m = S.fromList $ map nameToString nrs
  where
    nrs = runNoReturnAnalysis cg exitTest -- runIdentity (noReturnAnalysis cg exitTest)
    pta = runPointsToAnalysis m
    cg = callGraph m pta []
