-- Test polys...

{-# LANGUAGE DataKinds, FlexibleInstances, NoImplicitPrelude, OverloadedStrings, Trustworthy #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module TestPoly (firstPoly) where

import Prelude hiding (sqrt, quot, rem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck
import PastaCurves
import Poly

instance Arbitrary Fp where
  arbitrary = fromInteger <$> choose (0, 2 ^ (512::Integer))

instance Arbitrary Fq where
  arbitrary = fromInteger <$> choose (0, 2 ^ (512::Integer))

instance Arbitrary (Coefficients Fp) where
  arbitrary = do
    lll <- listOf1 arbitrary
    return $ Coefficients lll

firstPoly :: TestTree
firstPoly = testGroup "Testing first poly via QuickCheck" [
  testProperty "test polyAdd"  $ \a b -> polyAdd a b == (polyAdd b a :: Coefficients Fp),
  testProperty "test polySub"  $ \a b -> polySub a b == (polySub (polyNew [0 :: Fp]) (polySub b a)),
  testProperty "test polyMul"  $ \a b -> polyMul a b == (polyMul b a :: Coefficients Fp),
  testProperty "test polyAdd/Mul" $ \a b c -> polyMul (polyAdd a b) c == polyAdd (polyMul a c) (polyMul b c :: Coefficients Fp),
  testProperty "test polySub/Mul" $ \a b c -> polyMul (polySub a b) c == polySub (polyMul a c) (polyMul b c :: Coefficients Fp),
  testProperty "test polyDiv"  $ \a b -> polyDiv (polyMul a b) b == (a :: Coefficients Fp, Coefficients []),
  testProperty "test PolyDive2" $ \a b c -> polyDiv (polyAdd a b) c == div3 a b (c :: Coefficients Fp)
  ]

-- polyDiv testing is currently a bit hacky at best
div3 :: (Field a) => Coefficients a -> Coefficients a -> Coefficients a -> (Coefficients a, Coefficients a)
div3 a b c = (quot, rem)
  where
    (q_ac, r_ac) = polyDiv a c
    (q_bc, r_bc) = polyDiv b c
    r2 = polyAdd r_ac r_bc
    (q_r2, rem) = polyDiv r2 c
    quot = polyAdd (polyAdd q_ac q_bc) q_r2