{-# LANGUAGE DerivingStrategies, NoImplicitPrelude, ScopedTypeVariables #-}

module Poly (module Poly) where

import Prelude hiding (quot, rem)
import Data.List (dropWhileEnd)
import PastaCurves


-- | `Polynomial` is little-endian list of C₀, C₁, C₂ ... Cₙ field elements
newtype Polynomial a = Coefficients [a] deriving stock (Show, Eq)


-- | `polyNew` is a smart constructor that includes normalization, for export
polyNew :: (Field a) => [a] -> Polynomial a
polyNew x = Coefficients $ dropWhileEnd (==0) x


-- | `zipWithEqLen` zips two lists of equal length padded with "more significant 0s"
zipWithEqLen :: (Num a, Num b) => (a -> b -> c) -> [a] -> [b] -> [c]
zipWithEqLen fn a b = zipWith fn new_a new_b
  where
    pad = length a - length b
    new_a = a ++ replicate (-pad) 0
    new_b = b ++ replicate pad 0


-- | `polyAdd` adds two polynomials: coefficient by coefficient and drop leading zeros
polyAdd :: (Field a) => Polynomial a -> Polynomial a -> Polynomial a
polyAdd (Coefficients xx) (Coefficients yy) = polyNew $ zipWithEqLen (+) xx yy


-- | `polySub` subtracts two polynomials: coefficient by coefficient and drop leading zeros
polySub :: (Field a) => Polynomial a -> Polynomial a -> Polynomial a
polySub (Coefficients xx) (Coefficients yy) = polyNew $ zipWithEqLen (-) xx yy


-- | `polyMul` multiplies two polynomials: step through coefficient of x time polynomial y
polyMul :: (Field a) => Polynomial a -> Polynomial a -> Polynomial a
polyMul (Coefficients xx) (Coefficients yy) = polyNew (polyMul' xx yy)
  where
    polyMul' :: (Field a) => [a] -> [a] -> [a]
    polyMul' [] _ = []
    -- polyMul' _ [] = []
    polyMul' (x:xs) y = zipWithEqLen (+) (map (*x) y) (0 : polyMul' xs y)


-- | `polyScale` multiplies each coefficient by a constant
polyScale :: (Field a) => a -> Polynomial a -> Polynomial a
polyScale k (Coefficients x) = polyNew $ fmap (* k) x


-- TODO --> Adapt this to Maybe; Reconsider second polyDiv with [0] 
-- Divide two polynomials: dividend / divisor = result
polyDiv :: forall a. (Field a) => Polynomial a -> Polynomial a -> (Polynomial a, Polynomial a)
polyDiv _ (Coefficients []) = error "empty divisor, cannot divide by zero"
polyDiv _ (Coefficients [0]) = error "cannot divide by zero"
polyDiv (Coefficients []) _ = (polyNew [], polyNew [])
polyDiv (Coefficients dividend) (Coefficients divisor) = (polyNew quotient, polyNew remainder)
  where
    (quotient, remainder) = polyDiv' [] dividend
    polyDiv' :: [a] -> [a] -> ([a], [a])
    polyDiv' quot rem | null rem = (quot, rem)
    polyDiv' quot rem | length rem < length divisor = (quot, rem)
    polyDiv' quot rem = polyDiv' quot' rem'
      where
        k = last rem * inv0 (last divisor)
        shift = length rem - length divisor
        quot' = k : quot
        rem' = init $ zipWithEqLen (-) rem  (replicate shift 0 ++ fmap (* k) divisor)
