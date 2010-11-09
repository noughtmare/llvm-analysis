module Data.LLVM.PlaceholderTypes ( Identifier(..)
                                  , Value(..)
                                  , ValueT(..)
                                  , ConstantT(..)
                                  ) where

import Data.ByteString.Lazy (ByteString)
import Data.LLVM.AttributeTypes

-- These types are generated by the parser and will be
-- *temporary*.  They reference strings since that is all we have at
-- parse time.  These types will be replaced by direct references
-- after the entire AST is built and we can build the self-referential
-- graph structure.

data Identifier = LocalIdentifier ByteString
                | GlobalIdentifier ByteString
                  deriving (Show)

data Value = Value { valueName :: Identifier
                   , valueType :: Type
                   , valueContent :: ValueT
                   , valueOperands :: [Value]
                   }
           | ConstantValue { constantType :: Type
                           , constantContent :: ConstantT
                           }
           deriving (Show)

-- The first group of value types are unusual and are *not* "users".
-- This distinction is not particularly important for my purposes,
-- though, so I'm just giving all values a list of operands (which
-- will be empty for these things)
data ValueT = Argument [ParamAttribute]
            | BasicBlock ByteString [Value] -- Label, really instructions, which are values
            | InlineAsm ByteString ByteString -- ASM String, Constraint String; can parse constraints still
            -- | MDNode -- What is this?
            -- | MDString -- And this? Might not need either
            deriving (Show)

data ConstantT = BlockAddress Identifier Identifier -- Func Ident, Block Label -- to be resolved into something useful later
               | ConstantAggregateZero
               | ConstantArray [Value] -- This should have some parameters but I don't know what
               | ConstantExpr Value -- change this to something else maybe?  Value should suffice... might even eliminate this one
               | ConstantFP Double
               | ConstantInt Integer
               | ConstantPointerNull
               | ConstantStruct [Value] -- Just a list of other constants
               | ConstantVector [Value] -- again
               | UndefValue
               | MDNode [Value] -- A list of constants (and other metadata)
               | MDString ByteString
               | Function [Value] [FunctionAttribute] [ValueT] -- Arguments, function attrs, block list
               | GlobalVariable VisibilityStyle LinkageType ByteString
               | GlobalAlias VisibilityStyle LinkageType ByteString Value -- new name, real var
               | ConstantIdentifier Identifier -- Wrapper for globals - to be resolved later into a more useful direct references to a GlobalVariable
               deriving (Show)
