{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>

TODO
 - rework doc strings
 - refine calcS for variable widths
 - refine full protocol flow for variable widths (iterate)
 - last few protocol steps need polish

-}

{-# LANGUAGE RecordWildCards #-}

module PastaPoly (module PastaPoly) where

import PastaCurves
import System.Random.Stateful(mkStdGen, RandomGen)
import Data.List (mapAccumL)
import Data.Tuple (swap)

data CRS = CRS {degree:: Integer, crsG :: [Vesta], crsH :: Vesta}                                     -- set during startup
data ProverState = ProverState {a :: [Fp], b :: [Fp], g :: [Vesta], r :: Fp, lj :: [Fp], rj :: [Fp], d :: Fp, s :: Fp}  -- prover state evolves through 'dialogue'
data TranscriptState = TranscriptState {commitment :: Vesta, x :: Fp, ev :: Fp,                       -- initialized by prover
                       u :: Vesta, p' :: Vesta, uj :: [Fp], capLj :: [Vesta], capRj :: [Vesta],
                       capQ :: Vesta, capR :: Vesta, c :: Fp, z1 :: Fp, z2 :: Fp}      -- evolves through 'dialogue'
-- Verifier has no state (as it is essentially baked into the transcript)


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
    (r1, crsG) = mapAccumL (\rnd _ -> rndVesta rnd) rndGen [1..degree]
    (r2, crsH) = rndVesta r1


-- Initialize prover; return next rnd, private state along with public values in transcript state
prover0 :: RandomGen a => a -> CRS -> (a, ProverState, TranscriptState)
prover0 rndGen CRS{..} = (r3, ProverState {a=a, b=b, g=crsG, r=r, lj=[], rj=[], d=0, s=0},
  TranscriptState {commitment=commitment, x=x, ev=ev, u=neutral, p'=neutral, uj=[], capLj=[], capRj=[], capQ=neutral, capR=neutral, c=0, z1=0, z2=0})
  where
    (r1, a) = mapAccumL (\rnd _ -> rndF rnd) rndGen [1..degree]  -- random polynomial coeffs
    (r2, r) = rndF r1
    (r3, x) = rndF r2
    commitment = pointAdd (mulMul a crsG) (pointMul r crsH)
    b = [x^i | i <- [0..(degree-1)]]
    ev = foldr (\w v -> w + v * x) 0 a  -- evaluate using Horner's rule


-- verifier step 0: generate a random point 
verifier0 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier0 rndGen transcript = (r1, transcript {u=u, p'=p'})
    where
    (r1, u) = rndVesta rndGen
    p' = pointAdd (commitment transcript) (pointMul (ev transcript) u)


-- prover1 :: CRSv -> Polynomial Fp -> [Fp] -> Vesta -> (Vesta, Vesta)
prover1 :: (RandomGen a) => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
prover1 rndGen CRS{..} prover transcript = (r2, prover {lj=lj prover ++ [l0], rj=rj prover ++ [r0]},
  transcript {capLj=capLj transcript ++ [tLj], capRj=capRj transcript ++ [tRj]})
  where
    (a'hi, a'lo) = getHiLo $ a prover
    (b'hi, b'lo) = getHiLo $ b prover
    (g'hi, g'lo) = getHiLo $ g prover
    (r1, l0) = rndF rndGen
    (r2, r0) = rndF r1
    tLj = mulMul a'lo g'hi `pointAdd` pointMul l0 crsH `pointAdd` pointMul (inProd a'lo b'hi) (u transcript)
    tRj = mulMul a'hi g'lo `pointAdd` pointMul r0 crsH `pointAdd` pointMul (inProd a'hi b'lo) (u transcript)


verifier1 :: RandomGen a => a -> TranscriptState -> (a, TranscriptState)
verifier1 rndGen transcript = (r1, transcript {uj=uj transcript ++ [ujj]})
  where
    (r1, ujj) = rndF rndGen


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


prover2 :: RandomGen a => a -> CRS -> ProverState -> TranscriptState -> (a, ProverState, TranscriptState)
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
    result = [c * b * a | a <- [inv0 $ u !! 2, u !! 2], b <- [inv0 $ u !! 1, u !! 1], c <- [inv0 $ head u, head u]]


verNext :: TranscriptState -> (Vesta, TranscriptState)
verNext transcript = (result, transcript {capQ=result})
  where
    left = foldl1 pointAdd $ zipWith pointMul [z*z | z <- uj transcript] (capLj transcript)
    right = foldl1 pointAdd $ zipWith pointMul [inv0 (z*z) | z <- uj transcript] (capRj transcript)
    result = left `pointAdd` p' transcript `pointAdd` right


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


prvX0 :: RandomGen g => g -> CRS -> ProverState -> TranscriptState -> (g, ProverState, TranscriptState)
prvX0 rndGen crs prover transcript = (r2, prover{d=d, s=s}, transcript{capR=capR})
  where
    (r1, d) = rndF rndGen
    (r2, s) = rndF r1
    --bldS = calcS $ reverse (uj transcript)
    capG = head $ g prover -- mulMul bldS $ crsG crs
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
    s = calcS $ reverse (uj transcript)  -- TODO reverse
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
    s = calcS $ reverse (uj transcript8)  -- TODO reverse
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
