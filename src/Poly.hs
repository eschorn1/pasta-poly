{-# LANGUAGE DerivingStrategies, NoImplicitPrelude, ScopedTypeVariables #-}

module Poly (module Poly) where

import Prelude hiding (quot, rem)
import Data.List (dropWhileEnd)
import PastaCurves


-- Little endian list of C₀, C₁, C₂ ... Cₙ field elements; Not for export
newtype Coefficients a = Coefficients [a] deriving stock (Show, Eq)


-- Smart constructor includes normalization, for export
polyNew :: (Field a) => [a] -> Coefficients a
polyNew x = Coefficients $ dropWhileEnd (==0) x


-- pad lists to equal length with "more significant 0s", then perform operation
zipWithEqLen :: (Num a, Num b) => (a -> b -> c) -> [a] -> [b] -> [c]
zipWithEqLen fn a b = zipWith fn new_a new_b
  where
    pad = length a - length b
    new_a = a ++ replicate (-pad) 0
    new_b = b ++ replicate pad 0


-- Add two polynomials: coefficient by coefficient and drop leading zeros
polyAdd :: (Field a) => Coefficients a -> Coefficients a -> Coefficients a
polyAdd (Coefficients xx) (Coefficients yy) = polyNew $ zipWithEqLen (+) xx yy


-- Subtract two polynomials: coefficient by coefficient and drop leading zeros
polySub :: (Field a) => Coefficients a -> Coefficients a -> Coefficients a
polySub (Coefficients xx) (Coefficients yy) = polyNew $ zipWithEqLen (-) xx yy


-- Multiply two polynomials: step through coefficient of x time polynomial y
polyMul :: (Field a) => Coefficients a -> Coefficients a -> Coefficients a
polyMul (Coefficients xx) (Coefficients yy) = polyNew (polyMul' xx yy)
  where
    polyMul' :: (Field a) => [a] -> [a] -> [a]
    polyMul' [] _ = []
    -- polyMul' _ [] = []
    polyMul' (x:xs) y = zipWithEqLen (+) (map (*x) y) (0 : polyMul' xs y)


-- TODO --> Adapt this to Maybe; Reconsider second polyDiv with [0] 
-- Divide two polynomials: dividend / divisor = result
polyDiv :: forall a. (Field a) => Coefficients a -> Coefficients a -> (Coefficients a, Coefficients a)
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
