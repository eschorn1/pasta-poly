{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>

-- Algorithms and nomenclature matches section 3 of https://eprint.iacr.org/2019/1021


TODO
 - refine full protocol flow for variable widths (iterate)
 - last few protocol steps need recasting and polish

-}

{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}  -- thus, only list entries need to be initialized as empty


module PastaPoly (module PastaPoly) where

import PastaCurves
import System.Random.Stateful(mkStdGen, RandomGen)
import Data.List (mapAccumL)
import Data.Tuple (swap)
import Fft
import Poly


-- |  `CRS` is set once during initialization and remains stable
data CRS = CRS {degree:: Integer, crsG :: [Vesta], crsH :: Vesta}

-- | `ProverState` is private to the prover evolving through dialogue
data ProverState = ProverState {a, b :: [Fp], g :: [Vesta], r :: Fp, lj, rj :: [Fp], d, s :: Fp}

-- `TranscriptState` is a public record of prover<->verifier communication evolving though dialogue
data TranscriptState = TranscriptState {commitment :: Vesta, x, ev :: Fp,   -- fixed by prover
                       u, p' :: Vesta, uj :: [Fp], capLj, capRj :: [Vesta], -- evolve via iteration
                       capQ, capR :: Vesta, c, z1, z2 :: Fp}                -- evolves at finish

-- Verifier has no state (as it is essentially baked into the transcript)


-- | `getHiLo` splits a list of non-zero even length into a high half/portion and a low half/portion  
getHiLo :: [a] -> ([a],[a])
getHiLo a | odd (length a) || null a = error "getHiLo: can only split a list of non-zero even length"
getHiLo a = swap $ splitAt (length a `div` 2) a


-- | `mulMul` is the summed multiscalar multiplication of <a,G> vectors
mulMul :: (Curve g a) => [a] -> [g] -> g
mulMul a g | (length a /= length g) || null a = error "mulMul: non-empty lists must be of equal length"
mulMul a g = foldr1 pointAdd $ zipWith pointMul a g


-- | `innerProd` is the summed multiplication of <a,b> vectors
inProd :: (Field a) => [a] -> [a] -> a
inProd a b | (length a /= length b) || null a = error "inProd: non-empty lists must be of equal length"
inProd a b = sum $ zipWith (*) a b


-- | `setup` takes a degree and returns a CRS with a random G-vector and random H
setup :: RandomGen a => a -> Integer -> (a, CRS)
setup rndGen degree = (r2, CRS {degree=degree, crsG=crsG, crsH=crsH})
  where
    (r1, crsG) = mapAccumL (\rnd _ -> rndVesta rnd) rndGen [1..degree]
    (r2, crsH) = rndVesta r1


-- | 'prover0' initializes the prover state and places the commitment into an initialized transcript
prover0 :: RandomGen a => a -> CRS -> (a, ProverState, TranscriptState)
prover0 rndGen CRS{..} = (r3,
  ProverState {a=a, b=b, g=crsG, r=r, lj=[], rj=[]},
  TranscriptState {commitment=commitment, x=x, ev=ev, uj=[], capLj=[], capRj=[]})
  where
    (r1, a) = mapAccumL (\rnd _ -> rndF rnd) rndGen [1..degree]  -- random polynomial coeffs
    (r2, r) = rndF r1
    (r3, x) = rndF r2
    commitment = pointAdd (mulMul a crsG) (pointMul r crsH)
    b = [x^i | i <- [0..(degree-1)]]
    ev = foldr (\w v -> w + v * x) 0 a  -- evaluate using Horner's rule


-- | `verifier0` generate a random point, calculates p', and places into transcript
verifier0 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier0 rndGen transcript = (r1, transcript {u=u, p'=p'})
  where
    (r1, u) = rndVesta rndGen
    p' = pointAdd (commitment transcript) (pointMul (ev transcript) u)


-- | `prover1` chooses two random elements, calculates/appends corresponding capLj and capRj into transcript
prover1 :: (RandomGen a) => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover1 rndGen CRS{..} prover transcript = (r2,
  prover {lj=lj prover ++ [ljj], rj=rj prover ++ [rjj]},
  transcript {capLj=capLj transcript ++ [capLjj], capRj=capRj transcript ++ [capRjj]})
  where
    (a'hi, a'lo) = getHiLo (a prover)
    (b'hi, b'lo) = getHiLo $ b prover
    (g'hi, g'lo) = getHiLo $ g prover
    (r1, ljj) = rndF rndGen
    (r2, rjj) = rndF r1
    capLjj = mulMul a'lo g'hi `pointAdd` pointMul ljj crsH `pointAdd` pointMul (inProd a'lo b'hi) (u transcript)
    capRjj = mulMul a'hi g'lo `pointAdd` pointMul rjj crsH `pointAdd` pointMul (inProd a'hi b'lo) (u transcript)


-- | `verifier1` chooses random uj and appends into transcript
verifier1 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier1 rndGen transcript = (r1, transcript {uj=uj transcript ++ [ujj]})
  where
    (r1, ujj) = rndF rndGen


-- | `proverShrink` using the most recent uj element from the verifier, this halves provers' a, b and g
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


-- | `prover2` is called repeatedly to 'shrink' then calculate next capRj and capLj per `prover1`
prover2 :: RandomGen a => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover2 rndGen crs prover transcript = (r1, nextProver2, nextTranscript)
  where
    nextProver = proverShrink prover transcript
    (r1, nextProver2, nextTranscript) = prover1 rndGen crs nextProver transcript


-- | `prover3` does final shrink
prover3 :: ProverState -> TranscriptState -> ProverState
prover3 = proverShrink


-- | `calcWideS` converts list of uj into expanded binary vector
calcWideS :: [Fp] -> [Fp]
calcWideS u = helper u [1]
  where
    helper [] r = r
    helper (x:xs) r = helper xs $ fmap (* inv0 x) r ++ fmap (* x) r


-- | `verNext` demonstrates the verifier's ability to calculate Q based solely on transcript 
verNext :: TranscriptState -> (Vesta, TranscriptState)
verNext transcript = (result, transcript {capQ=result})
  where
    left = foldl1 pointAdd $ zipWith pointMul [z*z | z <- uj transcript] (capLj transcript)
    right = foldl1 pointAdd $ zipWith pointMul [inv0 (z*z) | z <- uj transcript] (capRj transcript)
    result = left `pointAdd` p' transcript `pointAdd` right


-- | `prvNext` has the prover calculating the synthetic r'
prvNext :: ProverState -> TranscriptState -> Fp
prvNext ProverState{..} TranscriptState{..} = result
  where
    left = sum $ zipWith (*) lj [z*z | z <- uj]
    right = sum $ zipWith (*) rj [inv0 (z*z) | z <- uj]
    result = left + r + right


-- | `prvLast` demonstrates the prover's ability to calculate Q 
prvLast :: CRS -> ProverState -> TranscriptState -> Fp -> Vesta
prvLast CRS{..} ProverState{..} transcript r' = result
  where
    result = pointMul (head a) (pointAdd (head g) (pointMul (head b) (u transcript))) `pointAdd` pointMul r' crsH


prvX0 :: RandomGen g => g -> CRS -> ProverState -> TranscriptState -> (g, ProverState, TranscriptState)
prvX0 rndGen crs prover transcript = (r2, prover{d=d, s=s}, transcript{capR=capR})
  where
    (r1, d) = rndF rndGen
    (r2, s) = rndF r1
    capG = head $ g prover
    capR = pointMul d (capG `pointAdd` pointMul (head $ b prover) (u transcript)) `pointAdd` pointMul s (crsH crs)


verX0 :: RandomGen g => g -> TranscriptState -> (g, TranscriptState)
verX0 rndGen transcript = (r1, transcript {c=c})
  where
    (r1, c) = rndF rndGen


prvX1 :: ProverState -> TranscriptState -> TranscriptState
prvX1 prover transcript = transcript {z1=z1, z2=z2}
  where
    z1 = head (a prover) * c transcript + d prover
    left = sum $ zipWith (*) (lj prover) [z*z | z <- uj transcript]
    right = sum $ zipWith (*) (rj prover) [inv0 (z*z) | z <- uj transcript]
    r' = left + r prover + right
    z2 = c transcript * r' + s prover


verAccept :: CRS -> TranscriptState -> Bool
verAccept crs transcript = result
  where
    left = pointMul (c transcript) (capQ transcript) `pointAdd` capR transcript
    s = calcWideS $ reverse (uj transcript)  -- TODO reverse
    sg = mulMul s $ crsG crs
    capG = sg
    sb = inProd s $ [x transcript ^ i | i <- [0..(degree crs - 1)]]
    right = pointMul (z1 transcript) (capG `pointAdd` pointMul sb (u transcript)) `pointAdd` pointMul (z2 transcript) (crsH crs)
    result = left == right


test :: Bool
test = result
  where
    (r1, crs) = setup (mkStdGen 1) 8                                             -- crs = (8-vector of g, h)
    (r2, proverState0, transcript1) = prover0 r1 crs
    (r3, transcript2) = verifier0 r2 transcript1
    (r4, proverState1, transcript3) = prover1 r3 crs proverState0 transcript2    -- now 8 wide
    (r5, transcript4) = verifier1 r4 transcript3
    (r6, proverState2, transcript5) = prover2 r5 crs proverState1 transcript4    -- now 4 wide
    (r7, transcript6) = verifier1 r6 transcript5
    (r8, proverState3, transcript7)  = prover2 r7 crs proverState2 transcript6   -- now 2 wide
    (r9, transcript8) = verifier1 r8 transcript7
    proverState4 = prover3 proverState3 transcript8                              -- now 1 wide
    s = calcWideS $ reverse (uj transcript8)  -- TODO reverse
    sg = mulMul s $ crsG crs
    sb = inProd s (b proverState0)
    (qVer, transcript9) = verNext transcript8
    r' = prvNext proverState4 transcript9
    qPrv = prvLast crs proverState4 transcript9 r'

    (ra, proverState5, transcript10) = prvX0 r9 crs proverState4 transcript9
    (_rb, transcript11) = verX0 ra transcript10
    transcript12 = prvX1 proverState5 transcript11

    vA = verAccept crs transcript12

    result = qVer == qPrv && (sb == head (b proverState4)) && (sg == head (g proverState4)) && vA
