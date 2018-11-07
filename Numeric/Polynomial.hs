{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Polynomials of the form a + bx + cx² + dx³ + …

module Numeric.Polynomial
    ( Coefficients (..)
    , Evaluate (..)
    , HasDerivative (..)
    , HasIntegral (..)
    , Translate (..)
    , Knot, Poly (..), Poly0 (..)
    , Poly1 (..), Poly2 (..), Poly3 (..), Poly4 (..)
    , Poly5 (..), Poly6 (..), Poly7 (..), Poly8 (..)
    , Domain
    ) where

import Prelude
import GHC.Exts (Constraint)
import Control.Applicative
import Control.Monad.Reader ({-instance Reader (r ->)-})
import qualified Data.List as List
import qualified Data.Vector.Generic -- sort-of unused; needed by 7.4.2
import qualified Data.Vector.Generic.Mutable -- sort-of unused; needed by 7.4.2
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving
import Data.AdditiveGroup
import Data.VectorSpace
import GHC.Generics (Generic)
import Text.Printf
import Test.QuickCheck

type Knot a = ({-X-}a, {-Y-}a)

class Evaluate poly where
    evaluate :: (Domain poly a) => poly a -> a -> a

class HasDerivative poly where
    type DerivativeOf poly :: * -> *
    derivative :: (Domain poly a, Domain (DerivativeOf poly) a) => poly a -> DerivativeOf poly a

class Evaluate (IntegralOf poly) => HasIntegral poly where
    type IntegralOf poly :: * -> *
    indefinite :: (Domain poly a, Domain (IntegralOf poly) a) => poly a -> IntegralOf poly a
    integral
        :: (Domain poly a, Domain (IntegralOf poly) a)
        => Knot a -> poly a -> IntegralOf poly a

    {-# INLINE integral #-}
    default integral
        :: ( Translate (IntegralOf poly), Num a
                , Domain (IntegralOf poly) a, Domain poly a) =>
        Knot a -> poly a -> IntegralOf poly a
    integral (x, y) p = translate (y - evaluate indef x) indef where
        indef = indefinite p

type family Domain (f :: * -> *) a :: Constraint

-- vertically translate the polynomial
class Translate poly where
    translate :: (Num a, Domain poly a) => a -> poly a -> poly a

-- | Little-endian polynomial of unspecified order.
data Poly a = Poly{- {{{ -}
    { poly_coeffs :: [a]
    } deriving (Eq)

instance Coefficients Poly where
    coefficients = poly_coeffs

-- multiply/accumulate in the (->) Double reader monad
mac :: Num a => a -> (->) a a -> (->) a a
mac ac m = \ x -> ac + x * m x
{-# INLINE mac #-}
infixr 1 `mac`

instance Evaluate Poly where
    evaluate = List.foldr mac (return 0) . coefficients

instance HasDerivative Poly where
    type DerivativeOf Poly = Poly
    derivative (Poly coeffs) = Poly (zipWith (*) (drop 1 coeffs) (iterate (+1) 0))

instance HasIntegral Poly where
    type IntegralOf Poly = Poly
    indefinite (Poly coeffs) = Poly (0 : integralCoeffs) where
        integralCoeffs = zipWith (/) coeffs $ iterate (+1) 0

instance Translate Poly where
    translate dy (Poly coeffs) = Poly (a' : drop 1 coeffs) where
        a' = dy + case coeffs of
            [] -> 0
            a : _ -> a

instance PrintfArg a => Show (Poly a) where
    show (Poly coeffs) = List.intercalate "  " $
            zipWith (printf "%+.3e%s") coeffs xns where
        xn n = ' ' : 'x' : showSuperScript n
        xns = "" : " x" : map xn [2 ..]
        showSuperScript :: Int -> String
        showSuperScript = map toSups . show where
            toSups c = case c of
                { '0' -> '⁰'; '1' -> '¹'; '2' -> '²'; '3' -> '³'; '4' -> '⁴'
                ; '5' -> '⁵'; '6' -> '⁶'; '7' -> '⁷'; '8' -> '⁸'; '9' -> '⁹'
                ; '-' -> '⁻'; _   -> c
                }
{- }}} -}

-- | Internal use only.
class Coefficients poly where
    coefficients :: poly a -> [a]

-- | Specialised 1st-, 2nd-, 3rd-, 4th- and 5th-order polynomials
data Poly0 a = Poly0{- {{{ -}
    { poly0_a :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly1 a = Poly1{- {{{ -}
    { poly1_a, poly1_b :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly2 a = Poly2
    { poly2_a, poly2_b, poly2_c :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly3 a = Poly3
    { poly3_a, poly3_b, poly3_c, poly3_d :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly4 a = Poly4
    { poly4_a, poly4_b, poly4_c, poly4_d, poly4_e :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly5 a = Poly5
    { poly5_a, poly5_b, poly5_c, poly5_d, poly5_e, poly5_f :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly6 a = Poly6
    { poly6_a, poly6_b, poly6_c, poly6_d, poly6_e, poly6_f, poly6_g :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly7 a = Poly7
    { poly7_a, poly7_b, poly7_c, poly7_d, poly7_e, poly7_f, poly7_g, poly7_h :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

data Poly8 a = Poly8
    { poly8_a, poly8_b, poly8_c, poly8_d, poly8_e, poly8_f, poly8_g, poly8_h, poly8_i :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)
{- }}} -}

type instance Domain Poly a = Fractional a

type instance Domain Poly0 a = Fractional a

type instance Domain Poly1 a = Fractional a

type instance Domain Poly2 a = Fractional a

type instance Domain Poly3 a = Fractional a

type instance Domain Poly4 a = Fractional a

type instance Domain Poly5 a = Fractional a

type instance Domain Poly6 a = Fractional a

type instance Domain Poly7 a = Fractional a

type instance Domain Poly8 a = Fractional a

instance Coefficients Poly0 where{- {{{ -}
    coefficients Poly0 {..} = [poly0_a]

instance Coefficients Poly1 where
    coefficients Poly1 {..} = [poly1_a, poly1_b]

instance Coefficients Poly2 where
    coefficients Poly2 {..} = [poly2_a, poly2_b, poly2_c]

instance Coefficients Poly3 where
    coefficients Poly3 {..} = [poly3_a, poly3_b, poly3_c, poly3_d]

instance Coefficients Poly4 where
    coefficients Poly4 {..} = [poly4_a, poly4_b, poly4_c, poly4_d, poly4_e]

instance Coefficients Poly5 where
    coefficients Poly5 {..} = [poly5_a, poly5_b, poly5_c, poly5_d, poly5_e, poly5_f]

instance Coefficients Poly6 where
    coefficients Poly6 {..} = [poly6_a, poly6_b, poly6_c, poly6_d, poly6_e, poly6_f, poly6_g]

instance Coefficients Poly7 where
    coefficients Poly7 {..} = [poly7_a, poly7_b, poly7_c, poly7_d, poly7_e, poly7_f, poly7_g, poly7_h]

instance Coefficients Poly8 where
    coefficients Poly8 {..} = [poly8_a, poly8_b, poly8_c, poly8_d, poly8_e, poly8_f, poly8_g, poly8_h, poly8_i]
{- }}} -}

-- We mark evaluate INLINE[1] to work around the GHC bug:
--   https://ghc.haskell.org/trac/ghc/ticket/7803
-- We really want all calls to 'evaluate' to be specialized or inlined, but if
-- we mark it INLINE, the bug leaves unspecialized call in some cases.
-- INLINE[1] causes a call to evaluate look small during the initial phase
-- (phase 2), which allows these superclass methods to be inlined. Then, in the
-- next phase, the evaluate method itself can be inlined.

instance Evaluate Poly0 where{- {{{ -}
    evaluate = \ Poly0 {..} -> {-# CORE "Poly0.evaluate" #-}
        return poly0_a
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly1 where
    evaluate = \ Poly1 {..} -> {-# CORE "Poly1.evaluate" #-}
        poly1_a `mac` return poly1_b
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly2 where
    evaluate = \ Poly2 {..} -> {-# CORE "Poly2.evaluate" #-}
        poly2_a `mac` poly2_b `mac` return poly2_c
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly3 where
    evaluate = \ Poly3 {..} -> {-# CORE "Poly3.evaluate" #-}
        poly3_a `mac` poly3_b `mac` poly3_c `mac` return poly3_d
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly4 where
    evaluate = \ Poly4 {..} -> {-# CORE "Poly4.evaluate" #-}
        poly4_a `mac` poly4_b `mac` poly4_c `mac` poly4_d `mac` return poly4_e
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly5 where
    evaluate = \ Poly5 {..} -> {-# CORE "Poly5.evaluate" #-}
        poly5_a `mac` poly5_b `mac` poly5_c `mac` poly5_d `mac` poly5_e `mac` return poly5_f
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly6 where
    evaluate = \ Poly6 {..} -> {-# CORE "Poly6.evaluate" #-}
        poly6_a `mac` poly6_b `mac` poly6_c `mac` poly6_d `mac` poly6_e `mac` poly6_f `mac` return poly6_g
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly7 where
    evaluate = \ Poly7 {..} -> {-# CORE "Poly7.evaluate" #-}
        poly7_a `mac` poly7_b `mac` poly7_c `mac` poly7_d `mac` poly7_e `mac` poly7_f `mac` poly7_g `mac` return poly7_h
    {-# INLINE[1] evaluate #-}

instance Evaluate Poly8 where
    evaluate = \ Poly8 {..} -> {-# CORE "Poly8.evaluate" #-}
        poly8_a `mac` poly8_b `mac` poly8_c `mac` poly8_d `mac` poly8_e `mac` poly8_f `mac` poly8_g `mac` poly8_h `mac` return poly8_i
    {-# INLINE[1] evaluate #-}
{- }}} -}

instance HasDerivative Poly0 where{- {{{ -}
    type DerivativeOf Poly0 = Poly0
    {-# INLINE derivative #-}
    derivative _ = Poly0 0

instance HasDerivative Poly1 where
    type DerivativeOf Poly1 = Poly0
    derivative Poly1 {..} =
        Poly0 poly1_b
    {-# INLINE derivative #-}

instance HasDerivative Poly2 where
    type DerivativeOf Poly2 = Poly1
    derivative Poly2 {..} =
        Poly1 poly2_b (2 * poly2_c)
    {-# INLINE derivative #-}

instance HasDerivative Poly3 where
    type DerivativeOf Poly3 = Poly2
    derivative Poly3 {..} =
        Poly2 poly3_b (2 * poly3_c) (3 * poly3_d)
    {-# INLINE derivative #-}

instance HasDerivative Poly4 where
    type DerivativeOf Poly4 = Poly3
    derivative Poly4 {..} =
        Poly3 poly4_b (2 * poly4_c) (3 * poly4_d) (4 * poly4_e)
    {-# INLINE derivative #-}

instance HasDerivative Poly5 where
    type DerivativeOf Poly5 = Poly4
    derivative Poly5 {..} =
        Poly4 poly5_b (2 * poly5_c) (3 * poly5_d) (4 * poly5_e) (5 * poly5_f)
    {-# INLINE derivative #-}

instance HasDerivative Poly6 where
    type DerivativeOf Poly6 = Poly5
    derivative Poly6 {..} =
        Poly5 poly6_b (2 * poly6_c) (3 * poly6_d) (4 * poly6_e) (5 * poly6_f) (6 * poly6_g)
    {-# INLINE derivative #-}

instance HasDerivative Poly7 where
    type DerivativeOf Poly7 = Poly6
    derivative Poly7 {..} =
        Poly6 poly7_b (2 * poly7_c) (3 * poly7_d) (4 * poly7_e) (5 * poly7_f) (6 * poly7_g) (7 * poly7_h)
    {-# INLINE derivative #-}

instance HasDerivative Poly8 where
    type DerivativeOf Poly8 = Poly7
    derivative Poly8 {..} =
        Poly7 poly8_b (2 * poly8_c) (3 * poly8_d) (4 * poly8_e) (5 * poly8_f) (6 * poly8_g) (7 * poly8_h) (8 * poly8_i)
    {-# INLINE derivative #-}
{- }}} -}

instance HasIntegral Poly0 where{- {{{ -}
    type IntegralOf Poly0 = Poly1
    indefinite = \ Poly0 {..} ->
        Poly1 0 poly0_a
    {-# INLINE indefinite #-}

instance HasIntegral Poly1 where
    type IntegralOf Poly1 = Poly2
    indefinite = \ Poly1 {..} ->
        Poly2 0 poly1_a (poly1_b / 2)
    {-# INLINE indefinite #-}

instance HasIntegral Poly2 where
    type IntegralOf Poly2 = Poly3
    indefinite = \ Poly2 {..} ->
        Poly3 0 poly2_a (poly2_b / 2) (poly2_c / 3)
    {-# INLINE indefinite #-}

instance HasIntegral Poly3 where
    type IntegralOf Poly3 = Poly4
    indefinite = \ Poly3 {..} ->
        Poly4 0 poly3_a (poly3_b / 2) (poly3_c / 3) (poly3_d / 4)
    {-# INLINE indefinite #-}

instance HasIntegral Poly4 where
    type IntegralOf Poly4 = Poly5
    indefinite = \ Poly4 {..} ->
        Poly5 0 poly4_a (poly4_b / 2) (poly4_c / 3) (poly4_d / 4) (poly4_e / 5)
    {-# INLINE indefinite #-}

instance HasIntegral Poly5 where
    type IntegralOf Poly5 = Poly6
    indefinite = \ Poly5 {..} ->
        Poly6 0 poly5_a (poly5_b / 2) (poly5_c / 3) (poly5_d / 4) (poly5_e / 5) (poly5_f / 6)
    {-# INLINE indefinite #-}

instance HasIntegral Poly6 where
    type IntegralOf Poly6 = Poly7
    indefinite = \ Poly6 {..} ->
        Poly7 0 poly6_a (poly6_b / 2) (poly6_c / 3) (poly6_d / 4) (poly6_e / 5) (poly6_f / 6) (poly6_g / 7)
    {-# INLINE indefinite #-}

instance HasIntegral Poly7 where
    type IntegralOf Poly7 = Poly8
    indefinite = \ Poly7 {..} ->
        Poly8 0 poly7_a (poly7_b / 2) (poly7_c / 3) (poly7_d / 4) (poly7_e / 5) (poly7_f / 6) (poly7_g / 7) (poly7_h / 8)
    {-# INLINE indefinite #-}
{- }}} -}

instance Translate Poly0 where{- {{{ -}
    translate dy = \ p0 -> {-# CORE "Poly0.translate" #-}
        p0 {poly0_a = poly0_a p0 + dy}
    {-# INLINE translate #-}

instance Translate Poly1 where
    translate dy = \ p1 -> {-# CORE "Poly1.translate" #-}
        p1 {poly1_a = poly1_a p1 + dy}
    {-# INLINE translate #-}

instance Translate Poly2 where
    translate dy = \ p2 -> {-# CORE "Poly2.translate" #-}
        p2 {poly2_a = poly2_a p2 + dy}
    {-# INLINE translate #-}

instance Translate Poly3 where
    translate dy = \ p3 -> {-# CORE "Poly3.translate" #-}
        p3 {poly3_a = poly3_a p3 + dy}
    {-# INLINE translate #-}

instance Translate Poly4 where
    translate dy = \ p4 -> {-# CORE "Poly4.translate" #-}
        p4 {poly4_a = poly4_a p4 + dy}
    {-# INLINE translate #-}

instance Translate Poly5 where
    translate dy = \ p5 -> {-# CORE "Poly5.translate" #-}
        p5 {poly5_a = poly5_a p5 + dy}
    {-# INLINE translate #-}

instance Translate Poly6 where
    translate dy = \ p6 -> {-# CORE "Poly6.translate" #-}
        p6 {poly6_a = poly6_a p6 + dy}
    {-# INLINE translate #-}

instance Translate Poly7 where
    translate dy = \ p7 -> {-# CORE "Poly7.translate" #-}
        p7 {poly7_a = poly7_a p7 + dy}
    {-# INLINE translate #-}

instance Translate Poly8 where
    translate dy = \ p8 -> {-# CORE "Poly8.translate" #-}
        p8 {poly8_a = poly8_a p8 + dy}
    {-# INLINE translate #-}
{- }}} -}

instance Num a => AdditiveGroup (Poly1 a) where{- {{{ -}
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly1 0 0
    Poly1 a b ^+^ Poly1 a' b' = Poly1 (a + a') (b + b')
    negateV (Poly1 a b) = Poly1 (negate a) (negate b)

instance Num a => AdditiveGroup (Poly2 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly2 0 0 0
    Poly2 a b c ^+^ Poly2 a' b' c' = Poly2 (a + a') (b + b') (c + c')
    negateV (Poly2 a b c) = Poly2 (negate a) (negate b) (negate c)

instance Num a => AdditiveGroup (Poly3 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly3 0 0 0 0
    Poly3 a b c d ^+^ Poly3 a' b' c' d' = Poly3 (a + a') (b + b') (c + c') (d + d')
    negateV (Poly3 a b c d) = Poly3 (negate a) (negate b) (negate c) (negate d)

instance Num a => AdditiveGroup (Poly4 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly4 0 0 0 0 0
    Poly4 a b c d e ^+^ Poly4 a' b' c' d' e' = Poly4 (a + a') (b + b') (c + c') (d + d') (e + e')
    negateV (Poly4 a b c d e) = Poly4 (negate a) (negate b) (negate c) (negate d) (negate e)

instance Num a => AdditiveGroup (Poly5 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly5 0 0 0 0 0 0
    Poly5 a b c d e f ^+^ Poly5 a' b' c' d' e' f' = Poly5 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f')
    negateV (Poly5 a b c d e f) = Poly5 (negate a) (negate b) (negate c) (negate d) (negate e) (negate f)

instance Num a => AdditiveGroup (Poly6 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly6 0 0 0 0 0 0 0
    Poly6 a b c d e f g ^+^ Poly6 a' b' c' d' e' f' g' = Poly6 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') (g + g')
    negateV (Poly6 a b c d e f g) = Poly6 (negate a) (negate b) (negate c) (negate d) (negate e) (negate f) (negate g)

instance Num a => AdditiveGroup (Poly7 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly7 0 0 0 0 0 0 0 0
    Poly7 a b c d e f g h ^+^ Poly7 a' b' c' d' e' f' g' h' = Poly7 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') (g + g') (h + h')
    negateV (Poly7 a b c d e f g h) = Poly7 (negate a) (negate b) (negate c) (negate d) (negate e) (negate f) (negate g) (negate h)

instance Num a => AdditiveGroup (Poly8 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = Poly8 0 0 0 0 0 0 0 0 0
    Poly8 a b c d e f g h i ^+^ Poly8 a' b' c' d' e' f' g' h' i' = Poly8 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') (g + g') (h + h') (i + i')
    negateV (Poly8 a b c d e f g h i) = Poly8 (negate a) (negate b) (negate c) (negate d) (negate e) (negate f) (negate g) (negate h) (negate i)
{- }}} -}

instance Num a => VectorSpace (Poly1 a) where{- {{{ -}
    type Scalar (Poly1 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly1 a b = Poly1 (s * a) (s * b)

instance Num a => VectorSpace (Poly2 a) where
    type Scalar (Poly2 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly2 a b c = Poly2 (s * a) (s * b) (s * c)

instance Num a => VectorSpace (Poly3 a) where
    type Scalar (Poly3 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly3 a b c d = Poly3 (s * a) (s * b) (s * c) (s * d)

instance Num a => VectorSpace (Poly4 a) where
    type Scalar (Poly4 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly4 a b c d e = Poly4 (s * a) (s * b) (s * c) (s * d) (s * e)

instance Num a => VectorSpace (Poly5 a) where
    type Scalar (Poly5 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly5 a b c d e f = Poly5 (s * a) (s * b) (s * c) (s * d) (s * e) (s * f)

instance Num a => VectorSpace (Poly6 a) where
    type Scalar (Poly6 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly6 a b c d e f g = Poly6 (s * a) (s * b) (s * c) (s * d) (s * e) (s * f) (s * g)

instance Num a => VectorSpace (Poly7 a) where
    type Scalar (Poly7 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly7 a b c d e f g h = Poly7 (s * a) (s * b) (s * c) (s * d) (s * e) (s * f) (s * g) (s * h)

instance Num a => VectorSpace (Poly8 a) where
    type Scalar (Poly8 a) = a
    {-# INLINE (*^) #-}
    s *^ Poly8 a b c d e f g h i = Poly8 (s * a) (s * b) (s * c) (s * d) (s * e) (s * f) (s * g) (s * h) (s * i)
{- }}} -}

{- {{{ -}-- unboxed Vector Poly[1-5]
#define derivingUnbox_(typ, targ, rep, tpat, rpat) \
    derivingUnbox "typ" [t| forall r. (Unbox r) => typ targ -> rep |] \
    [| \ (tpat) -> rpat |] [| \ rpat -> tpat |]
derivingUnbox_(Poly1,r,(r, r),Poly1 a b,(a,b))
derivingUnbox_(Poly2,r,(r, r, r),Poly2 a b c,(a,b,c))
derivingUnbox_(Poly3,r,(r, r, r, r),Poly3 a b c d,(a,b,c,d))
derivingUnbox_(Poly4,r,(r, r, r, r, r),Poly4 a b c d e,(a,b,c,d,e))
derivingUnbox_(Poly5,r,(r, r, r, r, r, r),Poly5 a b c d e f,(a,b,c,d,e,f))
derivingUnbox_(Poly6,r,(r, Poly5 r),Poly6 a b c d e f g,(a, Poly5 b c d e f g))
derivingUnbox_(Poly7,r,(r, r, Poly5 r),Poly7 a b c d e f g h,(a, b, Poly5 c d e f g h))
derivingUnbox_(Poly8,r,(r, r, r, Poly5 r),Poly8 a b c d e f g h i,(a, b, c, Poly5 d e f g h i))
{- }}} -}

instance Arbitrary a => Arbitrary (Poly1 a) where{- {{{ -}
    arbitrary = Poly1 <$> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly2 a) where
    arbitrary = Poly2 <$> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly3 a) where
    arbitrary = Poly3 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly4 a) where
    arbitrary = Poly4 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly5 a) where
    arbitrary = Poly5 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly6 a) where
    arbitrary = Poly6 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly7 a) where
    arbitrary = Poly7 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Poly8 a) where
    arbitrary = Poly8 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
{- }}} -}

-- General QuickCheck properties
-- prop_Evaluate :: (Evaluate poly, Coefficients poly) =>{- {{{ -}
--     a -> poly a -> Bool
-- prop_Evaluate x p = evaluate p x
--     == evaluate (Poly (coefficients p)) x

-- prop_Derivative :: (HasDerivative poly, Coefficients poly
--     , Coefficients (DerivativeOf poly)) => poly a -> Bool
-- prop_Derivative p = coefficients (derivative p)
--     == coefficients (derivative (Poly (coefficients p)))

-- prop_Integral :: (HasIntegral poly, Coefficients poly
--     , Coefficients (IntegralOf poly)) => poly a -> Bool
-- prop_Integral p = coefficients (indefinite p)
--     == coefficients (indefinite (Poly (coefficients p)))

-- prop_Translate :: (Evaluate poly, Translate poly) => a -> poly a -> a -> Bool
-- prop_Translate dy p x = abs (dy * 1.0e-10) >=
--     abs (evaluate p x + dy - evaluate (translate dy p) x)

-- _unused :: ()
-- _unused = ()
--     `const` (prop_Evaluate :: Double -> Double -> Bool)
--     `const` (prop_Derivative :: Double -> Bool)
--     `const` (prop_Integral :: Double -> Bool)
--     `const` (prop_Translate :: Double -> Double -> Double -> Bool)
{- }}} -}

{- {{{ -}{-
prop_Evaluate :: Double -> Poly1 -> Bool
prop_Evaluate :: Double -> Poly2 -> Bool
prop_Evaluate :: Double -> Poly3 -> Bool
prop_Evaluate :: Double -> Poly4 -> Bool
prop_Evaluate :: Double -> Poly5 -> Bool
prop_Integral :: Knot -> Double -> Bool
prop_Integral :: Knot -> Poly1 -> Bool
prop_Integral :: Knot -> Poly2 -> Bool
prop_Integral :: Knot -> Poly3 -> Bool
prop_Integral :: Knot -> Poly4 -> Bool
prop_Derivative :: Poly1 -> Bool
prop_Derivative :: Poly2 -> Bool
prop_Derivative :: Poly3 -> Bool
prop_Derivative :: Poly4 -> Bool
prop_Derivative :: Poly5 -> Bool
-}{- }}} -}
