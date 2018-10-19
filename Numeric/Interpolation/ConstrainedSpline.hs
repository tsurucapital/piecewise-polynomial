{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- | Constrained Cubic Splines: Taken from “Constrained Cubic Spline
-- Interpolation for Chemical Engineering Applications” by CJC Kruger.
-- Available from <http://www.korf.co.uk/spline.pdf>.

module Numeric.Interpolation.ConstrainedSpline
    ( constrainedSpline
    ) where

import Prelude
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V

import Numeric.Polynomial
import Numeric.Polynomial.Piecewise

constrainedSpline :: (Fractional a, Ord a, V.Unbox a) => Vector (Knot a) -> Piecewise Poly3 a
constrainedSpline ks0n = case V.length ks0n >= 3 of
    -- ensure we have at least three points
    True -> Piecewise $ V.zipWith4 segment f'all ks0m (V.unsafeTail f'all) ks1n
    False -> error "constrainedSpline: need at least 3 knots"
    where

    -- the knots are numbered 0, 1, 2, …, l, m, n
    ks1n = V.unsafeTail ks0n
    ks2n = V.unsafeTail ks1n
    ks0l = V.unsafeInit ks0m
    ks0m = V.unsafeInit ks0n
    ks1m = V.unsafeTail ks0m

    (x0, y0) = V.unsafeHead ks0n
    (x1, y1) = V.unsafeHead ks1n
    (xm, ym) = V.unsafeLast ks0m
    (xn, yn) = V.unsafeLast ks0n

    -- derivatives: at intermediate knots, and endpoints
    f'mid = V.zipWith3 f' ks0l ks1m ks2n -- f' at x1 to xm              {-7a-}
    f'x0 = (3/2) * (y1 - y0) / (x1 - x0) - (1/2) * f'x1                 {-7b-}
    f'x1 = V.unsafeHead f'mid
    f'xm = V.unsafeLast f'mid
    f'xn = (3/2) * (yn - ym) / (xn - xm) - (1/2) * f'xm                 {-7c-}
    f'all = V.concat [V.singleton f'x0, f'mid, V.singleton f'xn]
{-# INLINE constrainedSpline #-}

-- | The specified first-order derivative at some intermediate knot.
f' :: (Fractional a, Ord a) => Knot a -> Knot a -> Knot a -> a                                    {-7a-}
f' (x0, y0) (x1, y1) (x2, y2) = case slope01 * slope12 <= 0 of
    True -> 0 -- slopes change sign, or at least one is flat
    False -> 2 / (recip slope01 + recip slope12)
    where
    slope01 = (y1 - y0) / (x1 - x0)
    slope12 = (y2 - y1) / (x2 - x1)
{-# INLINE f' #-}

-- | Takes two knots and the first-order derivatives at each respective
-- /x/-coordinate, and produces the ‘constrained’ cubic segment in-between.
segment :: Fractional a => a -> Knot a -> a -> Knot a -> Segment Poly3 a
segment f'x0 (x0, y0) f'x1 (x1, y1) = Segment {..} where
    seg_end = x1
    seg_poly = Poly3 a b c d

    dy = y1 - y0
    dx = x1 - x0
    slope = dy / dx
    x0x0 = x0 * x0

    f''x0 = 2 * (3 * slope - (f'x1 + 2 * f'x0)) / dx                    {-8-}
    f''x1 = 2 * ((2 * f'x1 + f'x0) - 3 * slope) / dx                    {-9-}

    d = (1/6) * (f''x1 - f''x0) / dx                                    {-10-}
    c = (1/2) * (x1 * f''x0 - x0 * f''x1) / dx                          {-11-}
    b = slope - c * (x1 + x0) - d * (x1 * x1 + x1 * x0 + x0x0)          {-12-}
    a = y0 - b * x0 - c * x0x0 - d * x0x0 * x0                          {-13-}
{-# INLINE segment #-}

{-
-- | Example from above white paper.
_distillationCurve :: Vector Knot
_distillationCurve = V.fromList [(0, 30), (10, 130), (30, 150), (50, 150), (70, 170), (90, 220), (100, 320)]
-}

