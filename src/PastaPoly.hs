{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>
-}

{-# LANGUAGE RecordWildCards #-}

module PastaPoly (module PastaPoly) where

import PastaCurves
import Commit
import Poly
import Data.ByteString.UTF8 (fromString)
import System.Random.Stateful(mkStdGen, Random(randomR), RandomGen)
import Data.List (mapAccumL)
import Data.Tuple (swap)


data ProverState = ProverState {privatePoly :: Polynomial Fp, commitment :: Vesta, ev :: Fp, a :: [Fp], b :: [Fp], g :: [Vesta], h :: Vesta, uP :: Vesta}
data VerifierState = VerifierState {uV :: Vesta, uj :: [Fp], lj :: [Vesta], rj :: [Vesta]}


rndFp :: (RandomGen g) => g -> (g, Fp)
rndFp rndGen = fromInteger <$> swap (randomR (0, vestaPrime - 1) rndGen)


someFunc :: IO ()
someFunc = do
       print "Sample executable for pasta-curves"
       print $ pointMul (2 ^ (200::Integer) - 1 :: Fq) (base :: Pallas)


-- get b vector, given degree and x
getB :: (Num a) => Integer -> a -> [a]
getB degree x = [x^i | i <- [0..(degree - 1)]]


getHiLo :: [a] -> ([a],[a])
getHiLo vec = (vecHi, vecLo)
  where
    vecHi = drop (div (length vec) 2) vec
    vecLo = take (div (length vec) 2) vec


-- Initialize prover; return next rnd/private state along with public values
proverInit :: RandomGen a => a -> CRSv -> (a, ProverState, (Vesta, Fp, Fp))
proverInit rndGen crs = (r3, nextState, (commitment, x, ev))
  where
    (r1, a) = mapAccumL (\rnd _ -> rndFp rnd) rndGen [1..(length (fst crs))]
    (r2, r) = rndFp r1
    (r3, x) = rndFp r2
    privatePoly = polyNew a
    commitment = commit crs privatePoly r
    b = getB 8 x
    ev = polyEval x privatePoly
    (g, h) = crs
    nextState = ProverState {uP = undefined, ..}


-- verifier step 0: generate a random point 
verifier0 :: RandomGen a => a -> (a, VerifierState, Vesta)
verifier0 rndGen = (r1, nextState, u)
    where
    (uInt, r1) = randomR (0, vestaPrime - 1) rndGen
    u = (hashToVesta . fromString) $ show uInt
    nextState = VerifierState {uj = [], uV=u, lj = [], rj = []}


-- prover1 :: CRSv -> Polynomial Fp -> [Fp] -> Vesta -> (Vesta, Vesta)
prover1 :: (RandomGen a) => a -> ProverState -> Vesta -> (a, Vesta, Vesta)
prover1 rndGen state u = (r2, lLj, rRj)
  where
    (a'hi, a'lo) = getHiLo $ a state
    (b'hi, b'lo) = getHiLo $ b state
    (g'hi, g'lo) = getHiLo $ g state
    (r1, lj) = rndFp rndGen
    (r2, rj) = rndFp r1
    lLj = multiMulti a'lo g'hi `pointAdd` pointMul lj (h state) `pointAdd` pointMul (innerProd a'lo b'hi) u
    rRj = multiMulti a'hi g'lo `pointAdd` pointMul rj (h state) `pointAdd` pointMul (innerProd a'hi b'lo) u


verifier1 :: RandomGen a => a -> VerifierState -> Vesta -> Vesta -> (a, VerifierState, Fp)
verifier1 rndGen VerifierState{..} llj rrj = (r1, nextState, ujj)
  where
    (r1, ujj) = rndFp rndGen
    nextState = VerifierState {uj=uj ++ [ujj], lj=lj ++ [llj], rj=rj ++ [rrj], uV = undefined}


proverShrink :: ProverState -> Fp -> ProverState
proverShrink ProverState{..} uj = nextState
  where
    (a'hi, a'lo) = getHiLo a
    (b'hi, b'lo) = getHiLo b
    (g'hi, g'lo) = getHiLo g
    ujInv = inv0 uj
    a' = zipWith (+) (fmap (* ujInv) a'hi) (fmap (* uj) a'lo)
    b' = zipWith (+) (fmap (* ujInv) b'lo) (fmap (* uj) b'hi)
    g' = zipWith pointAdd (fmap (pointMul ujInv) g'lo) (fmap (pointMul uj) g'hi)
    nextState = ProverState {a=a', b=b', g=g', ..}


prover2 :: (RandomGen a) => a -> ProverState -> Fp -> Vesta -> (a, ProverState, Vesta, Vesta)
prover2 rndGen state uj u = (r1, nextState, ll, rr)
  where
    nextState = proverShrink state uj
    (r1, ll, rr) = prover1 rndGen nextState u


calcS :: [Fp] -> [Fp] -- 3 into 8
calcS u = result
  where
    -- result = [(c, b, a) | a <- ["u3m", "u3"], b <- ["u2m","u2"], c <- ["u1m","u1"]]
    result = [c * b * a | a <- [inv0 $ u !! 2, u !! 2], b <- [inv0 $ u !! 1,u !! 1], c <- [inv0 $ head u,head u]]


-- [uj] -> [Lj] -> P' -> Rj -> Qver
verNext :: [Fp] -> [Vesta] -> Vesta -> [Vesta] -> Vesta
verNext uj lj p' rj = result
  where
    left = foldl1 pointAdd $ zipWith pointMul [x*x | x <- uj] lj 
    right = foldl1 pointAdd $ zipWith pointMul [inv0 (x*x) | x <- uj] rj
    result = left `pointAdd` p' `pointAdd` right


-- [lj] -> [uj] -> r -> [rj] -> r'
prvNext :: [Fp] -> [Fp] -> Fp -> [Fp] -> Fp
prvNext lj uj r rj = result
  where
    left = sum $ zipWith (*) lj [x*x | x <- uj]
    right = sum $ zipWith (*) rj [inv0 (x*x) | x <- uj]
    result = left + r + right


prvLast :: Fp -> Vesta -> Fp -> Vesta -> Fp -> Vesta -> Vesta -- > Qprv
prvLast a g b u r' h = result
  where
    result = pointMul a (pointAdd g (pointMul b u)) `pointAdd` pointMul r' h


test :: Bool
test = result
  where
    (r1, crs) = setup 8 (mkStdGen 1)                          -- crs = (8-vector of g, h)
    (r2, proverState0, (commit, x, ev)) = proverInit r1 crs
    (r3, verifierState0, u) = verifier0 r2
    (r4, lLj1, rRj1) = prover1 r3 proverState0 u                    -- now 8 wide
    (r5, verifierState1, uj1) = verifier1 r4 verifierState0 lLj1 rRj1
    (r6, proverState1, lLj2, rRj2) = prover2 r5 proverState0 uj1 u  -- now 4 wide
    (r7, verifierState2, uj2) = verifier1 r6 verifierState1 lLj2 rRj2
    (r8, proverState2, lLj3, rRj3) = prover2 r7 proverState1 uj2 u  -- now 2 wide
    (r9, verifierState3, uj3) = verifier1 r8 verifierState2 lLj3 rRj3
    (ra, proverState3, lLj4, rRj4) = prover2 r9 proverState1 uj3 u  -- now 1 wide
    result = calcS (uj verifierState3) == [4, 5, 9 :: Fp]
