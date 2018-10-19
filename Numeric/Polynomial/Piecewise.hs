{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Polynomials of the form a + bx + cx² + dx³ + …

module Numeric.Polynomial.Piecewise
    ( Piecewise (..)
    , Segment (..)
    , splitAt
    , evaluateV
    ) where

import Prelude hiding (splitAt)
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Bits (shiftR)
import Data.Function (on)
import qualified Data.Vector.Generic -- sort-of unused; needed by 7.4.2
import qualified Data.Vector.Generic.Mutable -- sort-of unused; needed by 7.4.2
import Data.Vector.Unboxed.Base (MVector (..), Vector (..), Unbox)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV
import Data.Vector.Unboxed.Deriving
import Data.AdditiveGroup
import Data.VectorSpace
import GHC.Generics
import Test.QuickCheck

import Numeric.Polynomial
import Numeric.Polynomial.Log -- for {-# SPECIALISE … #-}

-- | A 'Segment' of a piecewise 'Polynomial', valid for /begin/ ≤ @x@
-- < @seg_end@, where /begin/ is implicit from the previous segment, if any.

data Segment poly a = Segment{- {{{ -}
    { seg_end  :: {-- UNPACK #-} !a
    , seg_poly :: {-- UNPACK #-} !(poly a)
    } deriving (Eq, Show, Generic)

type instance Domain (Segment poly) a = (Domain poly a, Num a)

instance Evaluate poly => Evaluate (Segment poly) where
    evaluate = \ Segment {..} -> evaluate seg_poly
    {-# INLINE evaluate #-}

instance HasDerivative poly => HasDerivative (Segment poly) where
    type DerivativeOf (Segment poly) = Segment (DerivativeOf poly)
    derivative Segment {..} = Segment {seg_poly = derivative seg_poly, ..}
    {-# INLINE derivative #-}

instance (HasIntegral poly, Translate (IntegralOf poly)) => HasIntegral (Segment poly) where
    type IntegralOf (Segment poly) = Segment (IntegralOf poly)
    indefinite = \ Segment {..} ->
        Segment {seg_poly = indefinite seg_poly, ..}
    {-# INLINE indefinite #-}

instance Translate poly => Translate (Segment poly) where
    translate dy = \ Segment {..} ->
        Segment {seg_poly = translate dy seg_poly, ..}
    {-# INLINE translate #-}

derivingUnbox "Segment"
    [t| forall poly a. (Unbox (poly a), Unbox a) => Segment poly a -> (a, poly a) |]
    [| \ (Segment end p) -> (end, p) |] [| \ (end, p) -> Segment end p |]
{- }}} -}

-- | Piecewise polynomials. Each segment stores its excluded upper endpoint
-- @seg_end@, with the lower endpoint being implied by the previous one. The
-- lower endpoint of the whole polynomial is not stored.
--
-- Derivatives are taken piecewise. For the indefinite integrals, the
-- constants of integration are propagated under the assumption that the
-- result is continuous.

newtype Piecewise poly a = Piecewise {unPiecewise :: Vector (Segment poly a)} deriving (Generic, Show, Eq)

type instance Domain (Piecewise poly) a = (Domain (Segment poly) a, Unbox (poly a), Unbox a, Num a, Ord a)

instance NFData (Piecewise poly a)

instance (AdditiveGroup (poly a), Unbox (poly a), Ord a, Unbox a) => AdditiveGroup (Piecewise poly a) where
    {-# INLINE zeroV #-}
    zeroV = Piecewise V.empty
    {-# INLINE negateV #-}
    negateV = Piecewise . V.map (\ seg@Segment {..} -> seg {seg_poly = negateV seg_poly}) . unPiecewise
    {-# INLINE (^+^) #-}
    Piecewise as ^+^ Piecewise bs = Piecewise $ V.create $ do
            --  Here we place the if expression inside the call to V.create
            --  rather than outside, in order to prevent Stream Fusion from
            --  malfunctioning.
            --  See https://github.com/haskell/vector/issues/59
            if V.null as then V.thaw bs else if V.null bs then V.thaw as else
                MV.new (V.length as + V.length bs - 1) >>= merge where
        iMax = V.length as - 1
        jMax = V.length bs - 1
        merge :: forall s. MVector s (Segment poly a) -> ST s (MVector s (Segment poly a))
        merge mv = go 0 0 0 where
            go :: Int -> Int -> Int -> ST s (MVector s (Segment poly a))
            go n i j = do
                MV.unsafeWrite mv n ab
                if aLast && bLast
                    then return (MV.unsafeTake (succ n) mv)
                    else go (succ n) i' j'
              where
                a = V.unsafeIndex as i
                b = V.unsafeIndex bs j
                ab = Segment end (seg_poly a ^+^ seg_poly b)
                aLast = i >= iMax
                bLast = j >= jMax
                aNext = (seg_end a, succ i, j)
                bNext = (seg_end b, i, succ j)
                -- This extrapolates the last seg_poly past seg_end.
                (end, i', j') = case seg_end a `compare` seg_end b of
                    LT -> if aLast then bNext else aNext
                    GT -> if bLast then aNext else bNext
                    EQ -> (seg_end a, succ i `min` iMax, succ j `min` jMax)
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly1 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly2 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly3 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly4 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly5 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly6 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly7 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise Poly8 Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly1) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly2) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly3) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly4) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly5) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly6) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly7) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (Log Poly8) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly1) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly2) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly3) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly4) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly5) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly6) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly7) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise (IntOfLog Poly8) Double) #-}
    {-# SPECIALISE instance AdditiveGroup (Piecewise IntOfLogPoly4 Double) #-}

instance (VectorSpace (poly a), Unbox (poly a), Unbox a, Ord a) => VectorSpace (Piecewise poly a) where
    type Scalar (Piecewise poly a) = Scalar (poly a)
    {-# INLINE (*^) #-}
    (*^) s = Piecewise . V.map (\ seg@Segment {..} -> seg {seg_poly = s *^ seg_poly}) . unPiecewise
    {-# SPECIALISE instance VectorSpace (Piecewise Poly1 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly2 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly3 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly4 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly5 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly6 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly7 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise Poly8 Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly1) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly2) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly3) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly4) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly5) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly6) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly7) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (Log Poly8) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly1) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly2) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly3) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly4) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly5) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly6) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly7) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise (IntOfLog Poly8) Double) #-}
    {-# SPECIALISE instance VectorSpace (Piecewise IntOfLogPoly4 Double) #-}

(!) :: Unbox alpha => Vector alpha -> Int -> alpha
(!) = V.unsafeIndex
{-# INLINE (!) #-}

-- | Pick out the segment that includes x. If x is out of range, return the
-- closest one; i.e. extrapolate rather than interpolate.
--
-- The function is in continuation-passing style to avoid boxing.
pickSegment :: forall poly a r. (Unbox (poly a), Ord a, Unbox a)
    => Piecewise poly a
    -> a
    -> (Int -> Segment poly a -> r) -- continuation
    -> r
pickSegment (Piecewise !segments) !x cont = {-# CORE "Piecewise.pickSegment" #-}
        case len > 0 of
    True -> bin 0 (len - 1)
    False -> error "pickSegment: no segments to pick from"
    where
    len = V.length segments

    bin :: Int -> Int -> r
    bin l h = case l >= h of
        True -> cont h (segments ! h)
        False -> case x < seg_end (segments ! m) of
            True -> bin l m
            False -> bin (m + 1) h
            where
            m = shiftR (l + h) 1
{-# INLINE pickSegment #-}

-- | Splits a piecewise in two: @splitAt end p@ returns a pair defined @∀x.
-- x < end@ and @∀x. end ≤ x@ respectively. 'V.concat' of the two halves
-- should be equivalent to @p@, potentially with a redundant segment.
splitAt :: (Unbox (poly a), Unbox a, Ord a) => a ->
    Piecewise poly a -> (Piecewise poly a, Piecewise poly a)
splitAt end pp = (Piecewise *** Piecewise) $
    if not (V.null l) && end <= seg_end (V.unsafeLast l)
    -- Make sure seg_end strictly increases from one segment to the next.
    then (l, r) else (l `V.snoc` s {seg_end = end `min` seg_end s}, r) where
    (l, r) = V.splitAt i (unPiecewise pp)
    (i, s) = pickSegment pp end (,)
{-# INLINE splitAt #-}

evaluatePiecewise :: (Evaluate poly, Domain (Piecewise poly) a)
    => Piecewise poly a -> a -> a
evaluatePiecewise = \ pp x -> {-# CORE "Piecewise.evaluate" #-}
    pickSegment pp x $ \_ seg -> evaluate seg x
{-# INLINE [1] evaluatePiecewise #-}

instance (Evaluate poly) => Evaluate (Piecewise poly) where
    evaluate = evaluatePiecewise
    {-# INLINE [1] evaluate #-}

{-# INLINE evaluateV #-}
-- | Evaluate a piecewise at multiple successively increasing points.
-- When the latter is sufficiently densely wrt the former, this is faster
-- than doing a binary search of the segments every time, as evaluate does.
evaluateV
    :: forall poly a.
    (Unbox (poly a), Evaluate poly, Unbox a, Domain poly a, Ord a, Num a) =>
    Piecewise poly a -> Vector a -> Vector a
evaluateV !(Piecewise pp) xs
    | V.null pp = error "evaluateV: no segments to pick from!"
    | otherwise = V.map eval $ V.postscanl' nextSegment (0, 0) xs where

    nextSegment (!prevSeg, _) x = (seg, x)
        where
            !seg = findSeg prevSeg x

    findSeg !i !x
        | x < seg_end (V.unsafeIndex pp i) || i == lastSeg = i
        | otherwise = findSeg (i+1) x

    !lastSeg = V.length pp - 1

    eval (i, x) = evaluate (seg_poly (V.unsafeIndex pp i)) x

instance (HasDerivative poly) =>
        HasDerivative (Piecewise poly) where
    type DerivativeOf (Piecewise poly) = Piecewise (DerivativeOf poly)
    derivative x = Piecewise $ V.map derivative $ unPiecewise x
    {-# INLINE derivative #-}

instance (HasIntegral poly, Translate (IntegralOf poly) ) =>
        HasIntegral (Piecewise poly) where
    type IntegralOf (Piecewise poly) = Piecewise (IntegralOf poly)
    indefinite ((unPiecewise -> segs) :: Piecewise poly a)
        | V.null segs = Piecewise V.empty
        | otherwise = let
                !indef_0@Segment{seg_end} = indefinite $ V.unsafeIndex segs 0
                Piecewise intTail = integral (seg_end, evaluate indef_0 seg_end)
                    $ Piecewise $ V.unsafeTail segs
            in Piecewise $ V.cons indef_0 intTail
    {-# INLINE indefinite #-}

    integral knot0@(!_, !_) (Piecewise segs) = Piecewise $ V.create $ do
        ints <- MV.new len

        -- integrate the i-th segment and force it to pass through (x, y)
        let integrate knot@(!_, !_) i = when (i < len) $ do
                int@Segment {seg_end} <- integral knot <$> V.unsafeIndexM segs i
                MV.unsafeWrite ints i int
                integrate (seg_end, evaluate int seg_end) (i + 1)

        integrate knot0 0
        return ints
      where
        len = V.length segs
    {-# INLINE integral #-}

instance (Evaluate poly, Translate poly) =>
        Translate (Piecewise poly) where
    translate f = Piecewise . V.map (translate f) . unPiecewise
    {-# INLINE translate #-}
    {-# SPECIALISE instance Translate (Piecewise Poly1) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly2) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly3) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly4) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly5) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly6) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly7) #-}
    {-# SPECIALISE instance Translate (Piecewise Poly8) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly1)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly2)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly3)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly4)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly5)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly6)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly7)) #-}
    {-# SPECIALISE instance Translate (Piecewise (Log Poly8)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly1)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly2)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly3)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly4)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly5)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly6)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly7)) #-}
    {-# SPECIALISE instance Translate (Piecewise (IntOfLog Poly8)) #-}
    {-# SPECIALISE instance Translate (Piecewise IntOfLogPoly4) #-}

instance (Arbitrary (poly a), Arbitrary a) => Arbitrary (Segment poly a) where
    arbitrary = Segment <$> arbitrary <*> arbitrary

instance (Unbox a, Unbox (poly a), Arbitrary (poly a), Arbitrary a, Ord a) => Arbitrary (Piecewise poly a) where
    arbitrary = Piecewise . V.fromList . sortBy (comparing seg_end)
        <$> listOf1 arbitrary

instance NFData (Segment poly a) where
    rnf Segment{..} =
        seg_end `seq` seg_poly `seq` ()

-- prop_AdditiveGroup :: NonEmptyList (Segment Double) ->
--     NonEmptyList (Segment Double) -> Double -> Bool
-- prop_AdditiveGroup (NonEmpty as) (NonEmpty bs) x =
--         evaluate (as' ^+^ bs') x == evaluate as' x + evaluate bs' x where
--     as' = V.fromList $ sortBy (compare `on` seg_end) as
--     bs' = V.fromList $ sortBy (compare `on` seg_end) bs

-- _unused :: ()
-- _unused = ()
--     `const` prop_AdditiveGroup
