module Commit (module Commit) where


import Poly
import PastaCurves
import System.Random (Random(randomR), RandomGen, mkStdGen)
import Data.ByteString.UTF8 (fromString)
import Data.List (mapAccumL)
import Data.Tuple (swap)


-- | The CRS type: vector of random points [G in Vesta], a blinding point H in Vesta
type CRSv = ([Vesta], Vesta)


-- | `setup` returns a random CRS and random generator, given a degree and random generator
setup :: (RandomGen a) => Integer -> a -> (a, ([Vesta], Vesta))
setup degree rndGen = (r2, (ggPts, hPt))
  where
    (r1, ggInts) = mapAccumL (\rnd _ -> swap $ randomR (0, vestaPrime - 1) rnd) rndGen [1..degree]
    ggPts = (hashToVesta . fromString) . show <$> ggInts
    (hInt, r2) = randomR (0, vestaPrime - 1) r1
    hPt = (hashToVesta . fromString) $ show hInt


-- | `commit` returns a commitment point given a polynomial and blinding factor
commit :: CRSv -> Polynomial Fp -> Fp -> Vesta
commit crs (Coefficients p) r = pointAdd (multiMulti p (fst crs)) (pointMul r (snd crs))


-- | `multiMulti` is summed multiscalar multiplication of <a,G> vectors
multiMulti :: (Curve g a) => [a] -> [g] -> g
multiMulti a g | (length a /= length g) || null a = error "non-empty lists must be of equal length"
multiMulti a g = foldl1 pointAdd $ zipWith pointMul a g


-- | `innerProd` is summed multiplication of <a,b> vectors
innerProd :: (Field a) => [a] -> [a] -> a
innerProd a b | (length a /= length b) || null a = error "non-empty lists must be of equal length"
innerProd a b = sum $ zipWith (*) a b 


rr ::  (RandomGen b) => b -> Integer -> (b, [Integer])
rr rndGen count = mapAccumL (\rnd _ -> swap $ randomR (1, 6) rnd) rndGen [1..count]


-- | quick test that commits are additively homomorphic testing...
addHomomorphic :: Bool
addHomomorphic = result 
  where
    (_, crs) = setup 4 (mkStdGen 100)
    a = 101 :: Fp
    p1 = polyNew [1, 2, 3, 4 :: Fp]
    r1 = 99 :: Fp
    commit1 = pointMul a $ commit crs p1 r1
    b = 209 :: Fp
    p2 = polyNew [1, 2, 3, 4 :: Fp]
    r2 = 99 :: Fp
    commit2 = pointMul b $ commit crs p2 r2
    addCommit = commit crs (polyAdd (polyScale a p1) (polyScale b p2)) (a*r1 + b*r2)
    result = pointAdd commit1 commit2 == addCommit

