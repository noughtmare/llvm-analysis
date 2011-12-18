-- | Module defines helpers for creating transitive-closure style algorithms
module Data.TransitiveClosure ( markVisited ) where

import Data.Foldable ( Foldable, foldMap )
import Data.Monoid
import qualified Data.Set as S

-- | This is a combinator to allow easy implementation of
-- transitive-closure style algorithms.  Given a function @f@ and a
-- seed value, apply @f@ to the seed and transitively to all of the
-- results of that application, collecting all of the intermediate and
-- final results into some Foldable container.
markVisited :: (Ord a, Foldable t, Monoid (t a)) => (a -> t a) -> a -> t a
markVisited f = mark' S.empty
  where
    mark' visited a =
      case a `S.member` visited of
        True -> mempty
        False ->
          let vis' = S.insert a visited
              newVals = f a
          in newVals `mappend` foldMap (mark' vis') newVals