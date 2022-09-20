-- Test polys...

{-# LANGUAGE DataKinds, FlexibleInstances, NoImplicitPrelude, OverloadedStrings, Trustworthy #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module TestPoly (firstPoly, firstPoly2) where

import Prelude hiding (sqrt, quot, rem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck
import PastaCurves
import Poly
import Fft

instance Arbitrary Fp where
  arbitrary = fromInteger <$> choose (0, 2 ^ (512::Integer))

instance Arbitrary Fq where
  arbitrary = fromInteger <$> choose (0, 2 ^ (512::Integer))

instance Arbitrary (Polynomial Fp) where
  arbitrary = do
    vecLen <- choose (1, 8)
    lll <- vectorOf vecLen arbitrary
    return $ Coefficients lll

firstPoly :: TestTree
firstPoly = testGroup "Testing first poly via QuickCheck" [
  testProperty "test polyAdd"  $ \a b -> polyAdd a b == (polyAdd b a :: Polynomial Fp),
  testProperty "test polySub"  $ \a b -> polySub a b == (polySub (polyNew [0 :: Fp]) (polySub b a)),
  testProperty "test polyMul"  $ \a b -> polyMul a b == (polyMul b a :: Polynomial Fp),
  testProperty "test polyAdd/Mul" $ \a b c -> polyMul (polyAdd a b) c == polyAdd (polyMul a c) (polyMul b c :: Polynomial Fp),
  testProperty "test polySub/Mul" $ \a b c -> polyMul (polySub a b) c == polySub (polyMul a c) (polyMul b c :: Polynomial Fp),
  testProperty "test polyDiv"  $ \a b -> polyDiv (polyMul a b) b == (a :: Polynomial Fp, Coefficients []),
  testProperty "test PolyDive2" $ \a b c -> polyDiv (polyAdd a b) c == div3 a b (c :: Polynomial Fp)
  ]

-- polyDiv testing is currently a bit hacky at best
div3 :: (Field a) => Polynomial a -> Polynomial a -> Polynomial a -> (Polynomial a, Polynomial a)
div3 a b c = (quot, rem)
  where
    (q_ac, r_ac) = polyDiv a c
    (q_bc, r_bc) = polyDiv b c
    r2 = polyAdd r_ac r_bc
    (q_r2, rem) = polyDiv r2 c
    quot = polyAdd (polyAdd q_ac q_bc) q_r2



firstPoly2 :: TestTree
firstPoly2 = testGroup "Testing first poly2 via QuickCheck" [
  testProperty "test no FFT"  $ \a b -> gimme16Samples (polyMul a b) getDomain ==
                                 mul16 (gimme16Samples a getDomain) (gimme16Samples b getDomain),
  testProperty "test FFT"  $ \a b -> polyMul a b ==
                                 polyNew (ifft2 (mul16 (gimme16Samples a getDomain) (gimme16Samples b getDomain)) getDomain)
  ]
