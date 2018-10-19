{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}

module Numeric.Polynomial.Log
    ( Log (..)
    , IntOfLog (..)
    , IntOfLogPoly4 (..)
    , exp5Tail
    , exp5TailInline
    , doubleToFrac
    ) where

import Prelude
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving
import Data.AdditiveGroup
import Data.VectorSpace
import GHC.Generics
import GHC.Types (Double(..))

import Numeric.Polynomial

-- Polynomial of log of x.
newtype Log poly a = Log (poly a)
    deriving (Eq, Show, AdditiveGroup)

type instance Domain (Log poly) a = (Floating a, Domain poly a)
instance (Translate poly) => Translate (Log poly) where
    translate a = \(Log p) -> Log (translate a p)
    {-# INLINE translate #-}

derivingUnbox "LogP"
    [t| forall poly a. (Unbox (poly a)) => Log poly a -> poly a |]
    [| \(Log p) -> p |] [| Log |]

instance (Num a, VectorSpace (poly a)) => VectorSpace (Log poly a) where
    type Scalar (Log poly a) = Scalar (poly a)
    s *^ Log p = Log (s *^ p)
    {-# INLINE (*^) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly1 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly2 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly3 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly4 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly5 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly6 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly7 a) #-}
    {-# SPECIALISE instance Num a => VectorSpace (Log Poly8 a) #-}

instance (Evaluate poly) => Evaluate (Log poly) where
    evaluate (Log p) = evaluate p . log
    {-# INLINE[1] evaluate #-}
    {-# SPECIALISE instance Evaluate (Log Poly1) #-}
    {-# SPECIALISE instance Evaluate (Log Poly2) #-}
    {-# SPECIALISE instance Evaluate (Log Poly3) #-}
    {-# SPECIALISE instance Evaluate (Log Poly4) #-}
    {-# SPECIALISE instance Evaluate (Log Poly5) #-}
    {-# SPECIALISE instance Evaluate (Log Poly6) #-}
    {-# SPECIALISE instance Evaluate (Log Poly7) #-}
    {-# SPECIALISE instance Evaluate (Log Poly8) #-}

data IntOfLog poly a = IntOfLog
    { intlog_k :: {-- UNPACK #-} !a
    , intlog_p :: {-- UNPACK #-} !(poly a)
    } deriving (Eq, Show, Generic)

type instance Domain (IntOfLog poly) a = (Domain poly a, Floating a)

derivingUnbox "IntOfLog"
    [t| forall poly a. (Unbox (poly a), Unbox a) => IntOfLog poly a -> (a, poly a) |]
    [| \ (IntOfLog k p) -> (k, p) |] [| \ (k, p) -> IntOfLog k p |]

instance (AdditiveGroup (poly a), Num a) => AdditiveGroup (IntOfLog poly a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = IntOfLog 0 zeroV
    IntOfLog k p ^+^ IntOfLog k' p' = IntOfLog (k + k') (p ^+^ p')
    negateV (IntOfLog k p) = IntOfLog (negate k) (negateV p)
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly1 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly2 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly3 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly4 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly5 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly6 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly7 a) #-}
    {-# SPECIALISE instance Num a => AdditiveGroup (IntOfLog Poly8 a) #-}

instance (VectorSpace (poly a), Scalar (poly a) ~ a, Num a) => VectorSpace (IntOfLog poly a) where
    type Scalar (IntOfLog poly a) = a
    {-# INLINE (*^) #-}
    s *^ IntOfLog k p = IntOfLog (s * k) (s *^ p)

instance (Evaluate poly) => Evaluate (IntOfLog poly) where
    evaluate = \ IntOfLog {..} x ->
        intlog_k  +  x * evaluate intlog_p (log x)
    {-# INLINE[1] evaluate #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly1) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly2) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly3) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly4) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly5) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly6) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly7) #-}
    {-# SPECIALISE instance Evaluate (IntOfLog Poly8) #-}

{-| ∫ f(α log(x)) dx

Take z ≡ α log(x); note that x = exp(z/α) and dx = x/α dz:

    ∫ f(α log(x)) dx                    ={ change variable: dx = x/α dz }
    ∫ f(z) x/α dz                       ={ integration by parts }
    f(z) x - α ∫ f′(z) x/α dz           ={ repeat until f′ vanishes }
    f(z) x - α f′(z) x
        + α² f″(z) x - α³ f‴(z) x …     ={ sum up; factor out x = exp(z) }
      N
    x ∑ (-1)ˡ αˡ f⁽ˡ⁾(z) + κ            ={ suppose ∃g. g = ∑ (-1)ˡ αˡ f⁽ˡ⁾ }
     l=0
    x g(α, z) + κ

The function g is well-defined when ∃N. ∀l,z. l>N ⇒ f⁽ˡ⁾(z) = 0, i.e.
when f(z) is a polynomial of finite order N. Note that unlike f(z),
g(α,z) depends on α directly, as well as indirectly via z.

Taking d/dz g(α,z), we arrive at the following recurrence relation:

               N-1                         N
    g′(α,z)  =  ∑ (-1)ˡ αˡ f⁽ˡ⁺¹⁾(z)  =  - ∑ (-1)ˡ αˡ f⁽ˡ⁾(z) / α
               l=0                        l=1
                         N
           =  ( f(z)  -  ∑ (-1)ˡ αˡ f⁽ˡ⁾(z) ) / α  =  (f(z) - g(α,z)) / α
                        l=0

Taking further derivatives on both sides, we see that in general:

    α g⁽ⁿ⁺¹⁾(α,z)  =  f⁽ⁿ⁾(z) - g⁽ⁿ⁾(α,z)

Replacing n by n-1 and rearranging, the following recurrence emerges:

    g⁽ⁿ⁻¹⁾(α,z)  =  f⁽ⁿ⁻¹⁾(z) - α g⁽ⁿ⁾(α,z)

Let us write f_n and g_n(α) for the coefficients of zⁿ in the expansion of
f(z) and g(α,z) respectively. Noting that n!f_n = f⁽ⁿ⁾(0), and likewise for
g(α,z). the above simplifies to the following recurrence for g_n(α) in terms
of f_n:

    g_N(α)      = f_N
    g_{n-1}(α)  = f_{n-1} - α n g_n(α)

Corollary: f_{n-1} = g_{n-1}(α) + α n g_n(α)
NB: the implementation is vastly simplified by fixing α=1.

-}

-- Numerically-stable specialized version for N=4, α=1.
--
-- Let F(x) be an indefinite integral of (log x)^4. Using the formula above,
-- you get:
--    F(x) =
--    ∫ (log(x))^4 dx =
--    x(24 - 24 log x + 12 (log x)^2 - 4 (log x)^3 + (log x)^4)
-- However it is not numerically stable to use this directly, because around
-- x=1, you lose precision in the result because the constant component
-- dominates:
--    F(1) = 24, F'(1) = 0
-- To avoid this issue we further transform the expression:
--    F(x)                                                = {let t be (-log x)}
--    exp(-t)(24 + 24t + 12t^2 + 4t^3 + t^4)              =
--    24 exp(-t)(1 + t + (1/2)t^2 + (1/6)t^3 + (1/24)t^4) =
--    24 - 24 exp(-t)(exp(t) - 1 - t - (1/2)t^2 - (1/6)t^3 - (1/24)t^4)
-- Then we drop the constant term '24' (remember this is an indefinite integral),
-- and evaluate the rest using a Taylor expansion:
--    exp(t) - 1 - t - (1/2)t^2 - (1/6)t^3 - (1/24)t^4    =
--    (1/120)t^5 + (1/720)t^6 + (1/5040)t^7 + ...
-- Note that this is the same as the expansion of exp(t) except that the first
-- 5 terms are dropped.

data IntOfLogPoly4 a = IntOfLogPoly4
    { ilp4_k :: {-- UNPACK #-} !a -- ^ constant term
    , ilp4_a, ilp4_b, ilp4_c, ilp4_d :: {-- UNPACK #-} !a
    , ilp4_u :: {-- UNPACK #-} !a
    } deriving (Eq, Show, Generic)

type instance Domain IntOfLogPoly4 a = (Ord a, Floating a)

derivingUnbox "IntOfLogPoly4"
    [t| forall r. Unbox r => IntOfLogPoly4 r -> (r, r, r, r, r, r) |]
    [| \ (IntOfLogPoly4 k a b c d u) -> (k, a, b, c, d, u) |]
    [| \ (k, a, b, c, d, u) -> IntOfLogPoly4 k a b c d u |]

instance Num a => AdditiveGroup (IntOfLogPoly4 a) where
    {-# INLINE zeroV #-}
    {-# INLINE (^+^) #-}
    {-# INLINE negateV #-}
    zeroV = IntOfLogPoly4 0 0 0 0 0 0
    IntOfLogPoly4 k a b c d u ^+^ IntOfLogPoly4 k' a' b' c' d' u'
        = IntOfLogPoly4 (k+k') (a+a') (b+b') (c+c') (d+d') (u+u')
    negateV (IntOfLogPoly4 k a b c d u)
        = IntOfLogPoly4 (-k) (-a) (-b) (-c) (-d) (-u)

instance Num a => VectorSpace (IntOfLogPoly4 a) where
    type Scalar (IntOfLogPoly4 a) = a
    {-# INLINE (*^) #-}
    s *^ IntOfLogPoly4 k a b c d u
        = IntOfLogPoly4 (s*k) (s*a) (s*b) (s*c) (s*d) (s*u)

instance Evaluate IntOfLogPoly4 where
    evaluate (IntOfLogPoly4 k a b c d u) x = k + x * fun (- log x)
        where
            fun =
                0 `mac`
                a `mac`
                b `mac`
                c `mac`
                d `mac`
                ((u*) <$> exp5Tail)
    {-# INLINE[1] evaluate #-}

{-# RULES "exp5Tail/Double" exp5Tail = exp5TailDouble #-}

exp5TailDouble :: Double -> Double
exp5TailDouble x = exp5TailInline x

doubleToFrac :: (Fractional a) => Double -> a
doubleToFrac = realToFrac
{-# NOINLINE doubleToFrac #-}

{-# RULES "doubleToFrac/Double" doubleToFrac = id #-}

{-# NOINLINE exp5Tail #-}

-- | exp5Tail x = (exp x - 1 - x - (1/2)x^2 - (1/6)x^3 - (1/24)x^4) / x^5.
-- When x is close to 0, we use a Taylor expansion to avoid loss of precision.
exp5Tail :: (Floating a, Ord a) => a -> a
exp5Tail x = exp5TailInline x

{-# INLINE exp5TailInline #-}
{-# INLINE exp5TailAnal #-}
{-# INLINE exp5TailTaylor #-}
exp5TailInline :: (Floating a, Ord a) => a -> a
exp5TailInline x
    | doubleToFrac threshold0 < x && x < doubleToFrac threshold1 = exp5TailTaylor x
    -- ^ This does not actually make sense for anything but Double (and AD s Double)
    | otherwise = exp5TailAnal x

threshold0 :: Double
threshold0 = D# -1.71##

threshold1 :: Double
threshold1 = D# 1.72##

-- | Calculate exp5Tail using the standard 'exp' function.
exp5TailAnal :: (Floating a) => a -> a
exp5TailAnal = (. recip) $
    0 `mac`
    (-1/24) `mac`
    (-1/6) `mac`
    (-1/2) `mac`
    (-1) `mac`
    (subtract 1 . exp . recip)

exp5TailTaylor :: (Fractional a, Num a) => a -> a
exp5TailTaylor =
    (1/120) `mac`
    (1/720) `mac`
    (1/5040) `mac`
    (1/40320) `mac`
    (1/362880) `mac`
    (1/3628800) `mac`
    (1/39916800) `mac`
    (1/479001600) `mac`
    (1/6227020800) `mac`
    (1/87178291200) `mac`
    (1/1307674368000) `mac`
    (1/20922789888000) `mac`
    (1/355687428096000) `mac`
    (1/6402373705728000) `mac`
    (1/121645100408832000) `mac`
    (1/2432902008176640000) `mac`
    return 0

-- multiply/accumulate in the (->) Double reader monad
mac :: Num a => a -> (->) a a -> (->) a a
mac ac m = \ x -> ac + x * m x
{-# INLINE mac #-}
infixr 1 `mac`

-- implementation for α = 1 only
instance HasIntegral (Log Poly) where
    type IntegralOf (Log Poly) = IntOfLog Poly
    indefinite (Log (Poly fs)) = IntOfLog 0 (Poly (reverse gs)) where
        n_fs = reverse (zip (iterate (+1) 0) fs) -- (n, f_{n-1})
        gs = zipWith (\ (n, f) g -> f - n * g) n_fs (0 : gs)

instance HasIntegral (Log Poly0) where
    type IntegralOf (Log Poly0) = IntOfLog Poly0
    indefinite = \ (Log poly0_a) -> IntOfLog 0 poly0_a
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly1) where
    type IntegralOf (Log Poly1) = IntOfLog Poly1
    indefinite = \ (Log (Poly1 {..})) -> let
        b = poly1_b
        a = poly1_a -     b
        in IntOfLog 0 (Poly1 a b)
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly2) where
    type IntegralOf (Log Poly2) = IntOfLog Poly2
    indefinite = \ (Log (Poly2 {..})) -> let
        c = poly2_c
        b = poly2_b - 2 * c
        a = poly2_a -     b
        in IntOfLog 0 (Poly2 a b c)
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly3) where
    type IntegralOf (Log Poly3) = IntOfLog Poly3
    indefinite = \ (Log (Poly3 {..})) -> let
        d = poly3_d
        c = poly3_c - 3 * d
        b = poly3_b - 2 * c
        a = poly3_a -     b
        in IntOfLog 0 (Poly3 a b c d)
    {-# INLINE indefinite #-}

-- NB: special case
instance HasIntegral (Log Poly4) where
    type IntegralOf (Log Poly4) = IntOfLogPoly4
    indefinite = \ (Log (Poly4 {..})) -> let
        a =    - poly4_a
        b = (a + poly4_b) * (1/2)
        c = (b - poly4_c) * (1/3)
        d = (c + poly4_d) * (1/4)
        u = (d - poly4_e) * 24
        in IntOfLogPoly4 0 a b c d u
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly5) where
    type IntegralOf (Log Poly5) = IntOfLog Poly5
    indefinite = \ (Log (Poly5 {..})) -> let
        f = poly5_f
        e = poly5_e - 5 * f
        d = poly5_d - 4 * e
        c = poly5_c - 3 * d
        b = poly5_b - 2 * c
        a = poly5_a -     b
        in IntOfLog 0 (Poly5 a b c d e f)
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly6) where
    type IntegralOf (Log Poly6) = IntOfLog Poly6
    indefinite = \ (Log (Poly6 {..})) -> let
        g = poly6_g
        f = poly6_f - 6 * g
        e = poly6_e - 5 * f
        d = poly6_d - 4 * e
        c = poly6_c - 3 * d
        b = poly6_b - 2 * c
        a = poly6_a -     b
        in IntOfLog 0 (Poly6 a b c d e f g)
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly7) where
    type IntegralOf (Log Poly7) = IntOfLog Poly7
    indefinite = \ (Log (Poly7 {..})) -> let
        h = poly7_h
        g = poly7_g - 7 * h
        f = poly7_f - 6 * g
        e = poly7_e - 5 * f
        d = poly7_d - 4 * e
        c = poly7_c - 3 * d
        b = poly7_b - 2 * c
        a = poly7_a -     b
        in IntOfLog 0 (Poly7 a b c d e f g h)
    {-# INLINE indefinite #-}

instance HasIntegral (Log Poly8) where
    type IntegralOf (Log Poly8) = IntOfLog Poly8
    indefinite = \ (Log (Poly8 {..})) -> let
        i = poly8_i
        h = poly8_h - 8 * i
        g = poly8_g - 7 * h
        f = poly8_f - 6 * g
        e = poly8_e - 5 * f
        d = poly8_d - 4 * e
        c = poly8_c - 3 * d
        b = poly8_b - 2 * c
        a = poly8_a -     b
        in IntOfLog 0 (Poly8 a b c d e f g h i)
    {-# INLINE indefinite #-}

instance Translate (IntOfLog poly) where
    translate dy (IntOfLog k p) = IntOfLog (k + dy) p
    {-# INLINE translate #-}

instance Translate IntOfLogPoly4 where
    translate dy (IntOfLogPoly4 k a b c d u)
        = IntOfLogPoly4 (k + dy) a b c d u
    {-# INLINE translate #-}

-- prop_IntOfLog ::
--     ( Coefficients p, HasIntegral (Log p)
--     , Coefficients q, IntegralOf (Log p) ~ IntOfLog q ) => p -> Bool
-- prop_IntOfLog p = intcoeff p == intcoeff (Poly (coefficients p)) where
--     intcoeff :: ( HasIntegral (Log p), Coefficients q
--         , IntegralOf (Log p) ~ IntOfLog q ) => p -> [Double]
--     intcoeff = coefficients . intlog_p . indefinite . Log

-- _unused :: ()
-- _unused = ()
--     `const` (prop_IntOfLog :: Double -> Bool)
