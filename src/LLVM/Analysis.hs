{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | This top-level module exports the LLVM IR definitions and some
-- basic functions to inspect the IR.  The sub-modules under
-- LLVM.Analysis provide higher-level tools for analyzing the IR.
module LLVM.Analysis (
  -- * Parsing LLVM Bitcode
  -- $parsing

  -- * Types
  module LLVM.Types,
  module LLVM.TypeInference,
  module LLVM.Utils,
  HasDefine (getDefine),
  defStmts,
  instructionOperands,
--  basicBlockInstructions,
  defExitStmts,
  bbTerminatorStmt,
  pattern ValInstr,

  -- * Extra helpers
  FuncLike(..),
  ToGraphviz(..)
  ) where

import Data.GraphViz ( DotGraph )
import LLVM.Types
import LLVM.Utils
import LLVM.TypeInference (HasType (getType))

-- TODO: move this trash to LLVM.Types

pattern ValInstr :: Instr -> Value
pattern ValInstr a <- Value { valValue = ValIdent (IdentValStmt Stmt { stmtInstr = a }) }

{-# INLINABLE bbTerminatorStmt #-}
bbTerminatorStmt :: BasicBlock -> Stmt
bbTerminatorStmt = last . bbStmts

defExitStmts :: Define -> [Stmt]
defExitStmts f = filter isRetStmt is
  where
    is = concatMap bbStmts (defBody f)
    isRetStmt Stmt { stmtInstr = Ret _ } = True
    isRetStmt Stmt { stmtInstr = Unreachable } = True
    isRetStmt _ = False


class HasDefine a where
  getDefine :: a -> Define

instance HasDefine Define where
  getDefine = id

instance HasDefine Argument where
  getDefine = error "Not yet implemented"

instance HasDefine BasicBlock where
  getDefine = error "Not yet implemented"


defStmts :: Define -> [Stmt]
defStmts Define {defBody = bbs} = bbStmts =<< bbs

-- basicBlockInstructions :: BasicBlock -> [Instr]
-- basicBlockInstructions BasicBlock { bbStmts = stmts } = map stmtInstr stmts

-- | Return all of the operands for an instruction.  Note that "special"
-- operands (like the 'Type' in a vararg inst) cannot be returned.  For
-- Phi nodes, only the incoming values (not their sources) are returned.
instructionOperands :: Instr -> [Value]
instructionOperands i =
  case i of
    Ret rv -> [rv]
    RetVoid -> []
    Arith _ lhs rhs -> [lhs, rhs]
    Bit _ lhs rhs -> [lhs, rhs]
    Conv _ cv _ -> [cv]
    Call _ _ fn args -> fn : args
    Alloca _ (Just n) _ -> [n]
    Alloca _ Nothing _ -> []
    Load la _ _ -> [la]
    Store sv sa _ _ -> [sv, sa]
    Fence _ _ -> []
    CmpXchg _ _ p nv c _ _ _ -> [p, nv, c]
    AtomicRW _ _ p v _ _ -> [p, v]
    ICmp _ v1 v2 -> [v1, v2]
    FCmp _ v1 v2 -> [v1, v2]
    Phi _ ivs -> map fst ivs
    GEP _ v ixs -> v : ixs
    Select c t e -> [c, t, e]
    ExtractValue a _ -> [a]
    InsertValue a v _ -> [a, v]
    ExtractElt v ix -> [v, ix]
    InsertElt v val ix -> [v, val, ix]
    ShuffleVector v1 v2 m -> [v1, v2, m]
    Jump _ -> []
    Br c _ _ -> [c]
    Invoke _ fn args _ _ -> fn : args
    Comment _ -> []
    Unreachable -> []
    Unwind -> []
    VaArg v _ -> [v]
    IndirectBr a _ -> [a]
    Switch v _ _ -> [v]
    LandingPad _ p _ cs -> maybe id (:) p $ map f cs where f (Catch x) = x; f (Filter x) = x
    Resume e -> [e]

-- | A class for types that can be derived from a Function.
class FuncLike a where
  fromDefine :: Define -> a

instance FuncLike Define where
  fromDefine = id

-- | A class for things that can be converted to graphviz graphs
class ToGraphviz a where
  toGraphviz :: a -> DotGraph Int

-- $parsing
--
-- The functions to parse LLVM Bitcode into a Haskell ADT are in the
-- llvm-data-interop package (in the "LLVM.Parse" module).  The first
-- is 'parseLLVMFile':
--
-- > import LLVM.Parse
-- > main = do
-- >   m <- parseLLVMFile defaultParserOptions filePath
-- >   either error analyzeModule
-- >
-- > analyzeModule :: Module -> IO ()
--
-- The 'defaultParserOptions' direct the parser to keep all metadata.
-- This behavior can be changed to discard the location metadata
-- normally attached to each instruction, saving a great deal of
-- space.  Metadata describing the source-level types of functions,
-- arguments, and local variables (among other things) is preserved.
-- If the module was compiled without debug information, no metadata
-- will be parsed at all.
--
-- There are two variants of 'parseLLVMFile':
--
--  * 'hParseLLVMFile' parses its input from a 'Handle' instead of
--    a named file.
--
--  * 'parseLLVM' parses its input from a (strict) 'ByteString'.
--
-- There is also a higher-level wrapper in
-- "LLVM.Analysis.Util.Testing":
--
-- > import LLVM.Analysis.Util.Testing
-- > import LLVM.Parse
-- > main = do
-- >   m <- buildModule ["-mem2reg", "-gvn"] (parseLLVMFile defaultParserOptions) filePath
-- >   either error analyzeModule
--
-- This wrapper function accepts both LLVM Bitcode and C/C++ source
-- files.  Source files are compiled with clang into bitcode; the
-- resulting bitcode is fed to the @opt@ binary, which is passed the
-- options in the first argument to 'buildModule'.
--
-- By default, this helper calls binaries named @clang@, @clang++@,
-- and @opt@, which are expected to be in your @PATH@.  To accommodate
-- distro packages, additional names are searched for @opt@:
-- @opt-3.2@, @opt-3.1@, and @opt-3.0@.
--
-- If you cannot place these binaries in your @PATH@, or if your
-- binaries have different names, you can specify them (either using
-- absolute or relative paths) with the environment variables
-- @LLVM_CLANG@, @LLVM_CLANGXX@, and @LLVM_OPT@.  These environment
-- variables override any default searching.
