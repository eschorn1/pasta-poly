{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>

TODO
 - get it working
 - there is probably a place where i reimplemente4d mulMul --> fix
 - separate public setup state from transcript

-}

{-# LANGUAGE RecordWildCards #-}

module PastaPoly (module PastaPoly) where

import PastaCurves
import System.Random.Stateful(mkStdGen, Random(randomR), RandomGen)
import Data.List (mapAccumL)
import Data.Tuple (swap)
import Debug.Trace (trace)

data CRS = CRS {degree:: Integer, crsG :: [Vesta], crsH :: Vesta}                                     -- set during startup
data ProverState = ProverState {a :: [Fp], b :: [Fp], g :: [Vesta], r :: Fp, lj :: [Fp], rj :: [Fp]}  -- prover state evolves through 'dialogue'
data TranscriptState = TranscriptState {commitment :: Vesta, x :: Fp, ev :: Fp,                       -- initialized by prover
                       u :: Vesta, p' :: Vesta, uj :: [Fp], capLj :: [Vesta], capRj :: [Vesta] }      -- evolves through 'dialogue'
-- Verifier has no state!!


rndFp :: (RandomGen g) => g -> (g, Fp)
rndFp rndGen = fromInteger <$> swap (randomR (0, vestaPrime - 1) rndGen)


rndVs :: (RandomGen g) => g -> (g, Vesta)
rndVs rndGen = hashToVesta . toBytesF <$> rndFp rndGen


getHiLo :: [a] -> ([a],[a])
getHiLo vec = swap $ splitAt (length vec `div` 2) vec


-- | `multiMulti` is summed multiscalar multiplication of <a,G> vectors
mulMul :: (Curve g a) => [a] -> [g] -> g
mulMul a g | (length a /= length g) || null a = error "mulMul: non-empty lists must be of equal length"
mulMul a g = foldl1 pointAdd $ zipWith pointMul a g


-- | `innerProd` is summed multiplication of <a,b> vectors
inProd :: (Field a) => [a] -> [a] -> a
inProd a b | (length a /= length b) || null a = error "inProd: non-empty lists must be of equal length"
inProd a b = sum $ zipWith (*) a b


-- Primary purpose is to setup the crs
setup :: RandomGen a => a -> Integer -> (a, CRS)
setup rndGen degree = (r2, CRS {degree=degree, crsG=crsG, crsH=crsH})
  where
    (r1, crsG) = mapAccumL (\rnd _ -> rndVs rnd) rndGen [1..degree]
    (r2, crsH) = rndVs r1


-- Initialize prover; return next rnd, private state along with public values in transcript state
prover0 :: RandomGen a => a -> CRS -> (a, ProverState, TranscriptState)
prover0 rndGen CRS{..} = (r3, ProverState {a=a, b=b, g=crsG, r=r, lj=[], rj=[]},
  TranscriptState {commitment=commitment, x=x, ev=ev, u=neutral, p'=neutral, uj=[], capLj=[], capRj=[]})
  where
    (r1, a) = mapAccumL (\rnd _ -> rndFp rnd) rndGen [1..degree]  -- random polynomial coeffs
    (r2, r) = rndFp r1
    (r3, x) = rndFp r2
    commitment = pointAdd (mulMul a crsG) (pointMul r crsH)
    b = [x^i | i <- [0..(degree-1)]]
    ev = foldr (\w v -> w + v * x) 0 a  -- evaluate using Horner's rule


-- verifier step 0: generate a random point 
verifier0 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier0 rndGen transcript = (r1, transcript {u=u, p'=p'})
    where
    (r1, u) = rndVs rndGen
    p' = pointAdd (commitment transcript) (pointMul (ev transcript) u)


-- prover1 :: CRSv -> Polynomial Fp -> [Fp] -> Vesta -> (Vesta, Vesta)
prover1 :: (RandomGen a) => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover1 rndGen CRS{..} prover transcript = (r2, prover {lj=lj prover ++ [l0], rj=rj prover ++ [r0]},
  transcript {capLj=capLj transcript ++ [tLj], capRj=capRj transcript ++ [tRj]})
  where
    (a'hi, a'lo) = getHiLo $ a prover
    (b'hi, b'lo) = getHiLo $ b prover
    (g'hi, g'lo) = getHiLo $ g prover
    (r1, l0) = rndFp rndGen  -- <<--- HANG ON, WE NEVER SAVE L0 AND R0; GONNA HAVE TO WIRE IN PROVER STATE OUTPUT!
    (r2, r0) = rndFp r1
    tLj = mulMul a'lo g'hi `pointAdd` pointMul l0 crsH `pointAdd` pointMul (inProd a'lo b'hi) (u transcript)
    tRj = mulMul a'hi g'lo `pointAdd` pointMul r0 crsH `pointAdd` pointMul (inProd a'hi b'lo) (u transcript)


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


prover2 :: (RandomGen a) => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover2 rndGen crs prover transcript = (r1, nextProver2, nextTranscript)
  where
    nextProver = proverShrink prover transcript
    (r1, nextProver2, nextTranscript) = prover1 rndGen crs nextProver transcript


prover3 :: ProverState -> TranscriptState -> ProverState
prover3 prover transcript = nextProver
  where
    nextProver = proverShrink prover transcript


calcS :: [Fp] -> [Fp] -- 3 into 8
calcS u = result
  where
    result = [c * b * a | a <- [inv0 $ u !! 2, u !! 2], b <- [inv0 $ u !! 1,u !! 1], c <- [inv0 $ head u,head u]]


verNext :: TranscriptState -> Vesta
verNext TranscriptState{..} = result
  where
    left = foldl1 pointAdd $ zipWith pointMul [z*z | z <- uj] capLj
    right = foldl1 pointAdd $ zipWith pointMul [inv0 (z*z) | z <- uj] capRj
    result = left `pointAdd` p' `pointAdd` right


prvNext :: ProverState -> TranscriptState -> Fp
prvNext ProverState{..} TranscriptState{..} = result
  where
    left = sum $ zipWith (*) lj [z*z | z <- uj]
    right = sum $ zipWith (*) rj [inv0 (z*z) | z <- uj]
    result = left + r + right


prvLast :: CRS -> ProverState -> TranscriptState -> Fp -> Vesta
prvLast CRS{..} ProverState{..} transcript r' = result
  where
    result = pointMul (head a) (pointAdd (head g) (pointMul (head b) (u transcript))) `pointAdd` pointMul r' crsH


test :: Bool
test = result
  where
    (r1, crs) = setup (mkStdGen 1) 8                          -- crs = (8-vector of g, h)
    (r2, proverState0, transcript1) = prover0 r1 crs
    (r3, transcript2) = verifier0 r2 transcript1
    (r4, proverState1, transcript3) = prover1 r3 crs proverState0 transcript2                -- now 8 wide
    (r5, transcript4) = verifier1 r4 transcript3
    (r6, proverState2, transcript5) = prover2 r5 crs proverState1 transcript4  -- now 4 wide
    (r7, transcript6) = verifier1 r6 transcript5
    (r8, proverState3, transcript7)  = prover2 r7 crs proverState2 transcript6  -- now 2 wide
    (_r9, transcript8) = verifier1 r8 transcript7
    proverState4 = prover3 proverState3 transcript8  -- now 1 wide
    s = calcS $ uj transcript8
    qVer = verNext transcript8
    r' = prvNext proverState4 transcript8
    qPrv = prvLast crs proverState4 transcript8 r'
    result =  qVer == qPrv --mulMul s (fst $ crs transcript8) == head ( fst (crs transcript8)) --    u transcript9 == u transcript1 -- = qVer == qPrv
