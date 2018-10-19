{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Numeric.Interpolation.Linear
    ( linear
    ) where

import Prelude
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V

import Numeric.Polynomial
import Numeric.Polynomial.Piecewise

{-# INLINE linear #-}
linear
    :: (Ord a, Fractional a, V.Unbox a) => Vector (Knot a) -> Piecewise Poly1 a
linear (forceIncreasing -> ks) = case V.length ks >= 2 of
    True -> Piecewise $ V.zipWith segment ks (V.unsafeTail ks)
    False -> error "linear: need at least 2 knots"

-- | Force X coordinates to have increasing values.
{-# INLINE forceIncreasing #-}
forceIncreasing
    :: (Ord a, Fractional a, V.Unbox a) => Vector (Knot a) -> Vector (Knot a)
forceIncreasing = V.postscanl step (-1/0, 777777{-not used-})
    where
        step (lastMax, _) (x, y) = (max lastMax x, y)

{-# INLINE segment #-}
segment :: (Eq a, Fractional a) => Knot a -> Knot a -> Segment Poly1 a
segment (x0, y0) (x1, y1) = Segment {..} where
    seg_end = x1
    seg_poly = translate (y0 - evaluate indef x0) indef
    indef = indefinite $ Poly0 $
        if x1 == x0 then 0 else (y1 - y0) / (x1 - x0)
