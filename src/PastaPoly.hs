{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>
-}

{-# LANGUAGE RecordWildCards #-}

module PastaPoly (module PastaPoly) where

import PastaCurves
import Data.ByteString.UTF8 (fromString)
import System.Random.Stateful(mkStdGen, Random(randomR), RandomGen)
import Data.List (mapAccumL)
import Data.Tuple (swap)


data ProverState = ProverState {a :: [Fp], b :: [Fp], g :: [Vesta], r :: Fp, lj :: [Fp], rj :: [Fp]}
-- Verifier has no state!!
data TranscriptState = TranscriptState {degree:: Integer, crs :: ([Vesta], Vesta), -- set during startup
                       commitment :: Vesta, x :: Fp, ev :: Fp,                     -- initialized by prover
                       u :: Vesta, p' :: Vesta, uj :: [Fp], capLj :: [Vesta], capRj :: [Vesta] } -- set via 'dialogue'

rndFp :: (RandomGen g) => g -> (g, Fp)
rndFp rndGen = fromInteger <$> swap (randomR (0, vestaPrime - 1) rndGen)


getHiLo :: [a] -> ([a],[a])
getHiLo vec = (vecHi, vecLo)
  where
    vecHi = drop (div (length vec) 2) vec
    vecLo = take (div (length vec) 2) vec


-- | `multiMulti` is summed multiscalar multiplication of <a,G> vectors
multiMulti :: (Curve g a) => [a] -> [g] -> g
multiMulti a g | (length a /= length g) || null a = error "non-empty lists must be of equal length"
multiMulti a g = foldl1 pointAdd $ zipWith pointMul a g


-- | `innerProd` is summed multiplication of <a,b> vectors
innerProd :: (Field a) => [a] -> [a] -> a
innerProd a b | (length a /= length b) || null a = error "non-empty lists must be of equal length"
innerProd a b = sum $ zipWith (*) a b


-- Primary purpose is to setup the crs
setup :: RandomGen a => a -> Integer -> (a, TranscriptState)
setup rndGen degree = (r2, TranscriptState {degree=degree, crs=crs,
  commitment=neutral, x=0, ev=0, u=neutral, p'=neutral, uj=[], capLj=[], capRj=[]})
--  commitment=undefined, x=undefined, ev=undefined, u=undefined, p'=undefined, uj=undefined, capLj=undefined, capRj=undefined})
  where
    (r1, gFps) = mapAccumL (\rnd _ -> rndFp rnd) rndGen [1..degree]
    gPts = (hashToVesta . fromString) . show <$> gFps
    (r2, hPt) = hashToVesta . toBytesF <$> rndFp r1
    crs = (gPts, hPt)


-- Initialize prover; return next rnd, private state along with public values in transcript state
prover0 :: RandomGen a => a -> TranscriptState -> (a, ProverState, TranscriptState)
prover0 rndGen transcript = (r3, ProverState {a=a, b=b, g=g, r=r, lj=[], rj=[]}, transcript {commitment=commitment, x=x, ev=ev})
  where
    (r1, a) = mapAccumL (\rnd _ -> rndFp rnd) rndGen [1..(degree transcript)]  -- random polynomial coeffs
    (r2, r) = rndFp r1
    (r3, x) = rndFp r2
    commitment = pointAdd (multiMulti a (fst $ crs transcript)) (pointMul r (snd $ crs transcript))
    b = [x^i | i <- [0..(degree transcript - 1)]]
    g = fst $ crs transcript
    ev = foldr (\w v -> w + v * x) 0 a


-- verifier step 0: generate a random point 
verifier0 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier0 rndGen transcript = (r1, transcript {u=u, p'=p'})
    where
    (r1, u) = hashToVesta . toBytesF <$> rndFp rndGen
    p' = pointAdd (commitment transcript) ( pointMul (ev transcript) u)


-- prover1 :: CRSv -> Polynomial Fp -> [Fp] -> Vesta -> (Vesta, Vesta)
prover1 :: (RandomGen a) => a -> ProverState -> TranscriptState -> (a, TranscriptState)
prover1 rndGen prover transcript = (r2, transcript {capLj=[lj], capRj=[rj]})
  where
    (b'hi, b'lo) = getHiLo $ b prover
    (a'hi, a'lo) = getHiLo $ a prover
    (g'hi, g'lo) = getHiLo $ g prover
    (r1, l0) = rndFp rndGen
    (r2, r0) = rndFp r1
    lj = multiMulti a'lo g'hi `pointAdd` pointMul l0 (snd $ crs transcript) `pointAdd` pointMul (innerProd a'lo b'hi) (u transcript)
    rj = multiMulti a'hi g'lo `pointAdd` pointMul r0 (snd $ crs transcript) `pointAdd` pointMul (innerProd a'hi b'lo) (u transcript)


verifier1 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier1 rndGen transcript = (r1, transcript {uj=uj transcript ++ [ujj]})
  where
    (r1, ujj) = rndFp rndGen


proverShrink :: ProverState -> TranscriptState -> ProverState
proverShrink prover transcript = prover {a=a', b=b', g=g'}
  where
    (a'hi, a'lo) = getHiLo $ a prover
    (b'hi, b'lo) = getHiLo $ b prover
    (g'hi, g'lo) = getHiLo $ g prover
    ujInv = inv0 $ last (uj transcript)
    a' = zipWith (+) (fmap (* ujInv) a'hi) (fmap (* last (uj transcript)) a'lo)
    b' = zipWith (+) (fmap (* ujInv) b'lo) (fmap (* last (uj transcript)) b'hi)
    g' = zipWith pointAdd (fmap (pointMul ujInv) g'lo) (fmap (pointMul (last (uj transcript))) g'hi)


prover2 :: (RandomGen a) => a -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover2 rndGen prover transcript = (r1, nextProver, nextTranscript)
  where
    nextProver = proverShrink prover transcript
    (r1, nextTranscript) = prover1 rndGen nextProver transcript


calcS :: [Fp] -> [Fp] -- 3 into 8
calcS u = result
  where
    -- result = [(c, b, a) | a <- ["u3m", "u3"], b <- ["u2m","u2"], c <- ["u1m","u1"]]
    result = [c * b * a | a <- [inv0 $ u !! 2, u !! 2], b <- [inv0 $ u !! 1,u !! 1], c <- [inv0 $ head u,head u]]


-- [uj] -> [Lj] -> P' -> Rj -> Qver
--verNext :: [Fp] -> [Vesta] -> Vesta -> [Vesta] -> Vesta
--verNext uj lj p' rj = result
verNext :: TranscriptState -> Vesta
verNext TranscriptState{..} = result
  where
    left = foldl1 pointAdd $ zipWith pointMul [x*x | x <- uj] capLj
    right = foldl1 pointAdd $ zipWith pointMul [inv0 (x*x) | x <- uj] capRj
    result = left `pointAdd` p' `pointAdd` right


-- [lj] -> [uj] -> r -> [rj] -> r'
-- prvNext :: [Fp] -> [Fp] -> Fp -> [Fp] -> Fp
-- prvNext lj uj r rj = result
prvNext :: ProverState -> TranscriptState -> Fp 
prvNext ProverState{..} TranscriptState{..} = result
  where
    left = sum $ zipWith (*) lj [x*x | x <- uj]
    right = sum $ zipWith (*) rj [inv0 (x*x) | x <- uj]
    result = left + r + right


-- prvLast :: Fp -> Vesta -> Fp -> Vesta -> Fp -> Vesta -> Vesta -- > Qprv
-- prvLast a g b u r' h = result
prvLast :: ProverState -> TranscriptState -> Fp -> Vesta
prvLast ProverState{..} transcript r' = result
  where
    result = pointMul (head a) (pointAdd (head g) (pointMul (head b) (u transcript))) `pointAdd` pointMul r' (snd $ crs transcript)


test :: Bool
test = result
  where
    (r1, transcript0) = setup (mkStdGen 1) 8                          -- crs = (8-vector of g, h)
    (r2, proverState0, transcript1) = prover0 r1 transcript0
    (r3, transcript2) = verifier0 r2 transcript1
    (r4, transcript3) = prover1 r3 proverState0 transcript2                    -- now 8 wide
    (r5, transcript4) = verifier1 r4 transcript3
    (r6, proverState2, transcript5) = prover2 r5 proverState0 transcript4  -- now 4 wide
    (r7, transcript6) = verifier1 r6 transcript5
    (r8, proverState3, transcript7) = prover2 r7 proverState2 transcript6  -- now 2 wide
    (r9, transcript8) = verifier1 r8 transcript7
    (_ra, proverState4, transcript9) = prover2 r9 proverState3 transcript8  -- now 1 wide
    s = calcS $ uj transcript9
    qVer = verNext transcript9
    r' = prvNext proverState4 transcript9
    qPrv = prvLast proverState4 transcript9 r'
    result = qVer == qPrv
