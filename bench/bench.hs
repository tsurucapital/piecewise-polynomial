module Main where

import qualified Data.Vector.Unboxed as V
import Numeric.Polynomial
import Numeric.Polynomial.Piecewise
import Numeric.Interpolation.Linear
import Numeric.Interpolation.ConstrainedSpline

import Criterion.Main

main :: IO ()
main = defaultMain
    [ bench "map-eval const (no spec)" $ whnf (V.map (evaluate p0)) xs
    , bench "PP.evalV const (no spec)" $ whnf (evaluateV p0)        xs
    , bench "map-eval linear"          $ whnf (V.map (evaluate p1)) xs
    , bench "PP.evalV linear"          $ whnf (evaluateV p1)        xs
    , bench "map-eval cubic"           $ whnf (V.map (evaluate p3)) xs
    , bench "PP.evalV cubic"           $ whnf (evaluateV p3)        xs
    ] where
    p0 = V.map (\ x -> Segment x x) xs -- no SPECIALISE for Piecewise Double
    p1 = linear (V.zip xs xs)
    p3 = constrainedSpline (V.zip xs xs)
    xs = V.fromList [0, 1 .. 50]

