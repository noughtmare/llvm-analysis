{-# LANGUAGE TypeOperators #-}
-- | Utilities to parse the type names used by LLVM.  Names are parsed
-- into the representation used by the Itanium ABI package.  This
-- representation can deal with namespace qualified names and supports
-- conversion between Strings and Names.
module LLVM.Analysis.Util.Names (
  parseTypeName,
  unparseTypeName,
  parseFunctionName,
  unparseFunctionName
  ) where

import Prelude hiding ( (.) )
import Control.Category ( (.) )
import Text.Boomerang
import Text.Boomerang.String

import ABI.Itanium as ABI
import LLVM.Analysis as LLVM

parseFunctionName :: Define -> Either String Name
parseFunctionName f =
  case demangleName fname of
    Left e -> Left e
    Right (ABI.Function sname _) -> Right sname
    Right (ABI.OverrideThunk _ (ABI.Function sname _)) -> Right sname
    Right n -> Left ("Unexpected name: " ++ show n)
  where
    Symbol fname = defName f

unparseFunctionName :: Name -> Maybe String
unparseFunctionName = unparseTypeName

parseTypeName :: String -> Either String Name
parseTypeName s =
  case parseString name s of
    Right n -> Right n
    Left e -> Left (show e)

unparseTypeName :: Name -> Maybe String
unparseTypeName = unparseString name

name :: Boomerang StringError String a (Name :- a)
name = ABI.rNestedName . rList qualifier . rList1 prefix . unqName <>
         ABI.rUnscopedName . unscopedName


unscopedName :: Boomerang StringError String a (UName :- a)
unscopedName = ABI.rUName . unqName

unqName :: Boomerang StringError String a (UnqualifiedName :- a)
unqName = ABI.rSourceName . rList1 (satisfy (/= ':'))

-- Just a hack since we know we won't have qualifiers.  It is fine if
-- it always fails because the empty list is allowed
qualifier :: Boomerang StringError String a (CVQualifier :- a)
qualifier = ABI.rConst . lit "@@INVALID@@"

prefix :: Boomerang StringError String a (Prefix :- a)
prefix = ABI.rUnqualifiedPrefix . unqName . lit "::"
