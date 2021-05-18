{-# LANGUAGE ViewPatterns #-}
module Main ( main ) where

import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as M
import Data.Monoid
import System.Environment ( getArgs, withArgs )
import System.FilePath
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.Dominance
import LLVM.Analysis.CFG
import LLVM.Analysis.Util.Testing
-- import LLVM.Parse

import Data.LLVM.BitCode (parseBitCode)
import Text.LLVM.Resolve (resolve)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.Either (fromRight)
import LLVM.Types
import System.IO
import Debug.Trace

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  args <- getArgs
  let pat = case args of
        [] -> "tests/block-return/*.c"
        [infile] -> infile
        _ -> error "Only one argument allowed"
      testDescriptors = [ TestDescriptor { testPattern = pat
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = blockRetMap
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

data Bundle = Bundle Define PostdominatorTree CFG

instance HasDefine Bundle where
  getDefine (Bundle f _ _) = f

instance HasPostdomTree Bundle where
  getPostdomTree (Bundle _ pdt _) = pdt

instance HasCFG Bundle where
  getCFG (Bundle _ _ cfg) = cfg

-- Take the first function in the module and summarize it (map of
-- block names to return values that are constant ints)
blockRetMap :: Module -> Map String Int
blockRetMap m = foldr (recordConstIntReturn brs) mempty blocks
  where
    f1 : _ = modDefines m
    blocks = defBody f1
    brs = labelBlockReturns bdl
    cfg = controlFlowGraph f1
    pdt = postdominatorTree cfg
    bdl = Bundle f1 pdt cfg

recordConstIntReturn :: BlockReturns -> BasicBlock -> Map String Int -> Map String Int
recordConstIntReturn brs bb m =
  case blockReturn brs bb of
    -- Just (Value _ _ (ValIdent (IdentValStmt Stmt {stmtInstr = i}))) | trace (show i) False -> undefined
    Just (valValue -> ValInteger iv) ->
      M.insert (bbName bb) (fromIntegral iv) m
    _ -> m
