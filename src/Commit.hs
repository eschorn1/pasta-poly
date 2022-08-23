module Commit (module Commit) where


import Poly
import PastaCurves
import System.Random
import Control.Monad (liftM2, replicateM)
import Data.ByteString.UTF8 (fromString)
import Data.List
import Data.Tuple


-- | The CRS type: vector of random points [G in Vesta], a blinding point H in Vesta
type CRSv = ([Vesta], Vesta)


-- | `setup` returns a random CRS
setup :: Int -> IO ([Vesta], Vesta)
setup d = liftM2 (,) gg h
  where
    gg = replicateM d $ (hashToVesta . fromString) . show <$> randomRIO (1, vestaPrime - 1)
    h = (hashToVesta . fromString) . show <$> randomRIO (1, vestaPrime - 1)


-- | `commit` returns a commitment point
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





-- | `go` provides handy testing...
go :: IO Bool --Vesta
go = do
    crs <- setup 4
    let a = 101 :: Fp
    let p1 = polyNew [1, 2, 3, 4 :: Fp]
    let r1 = 99 :: Fp
    let commit1 = pointMul a $ commit crs p1 r1
    let b = 209 :: Fp
    let p2 = polyNew [1, 2, 3, 4 :: Fp]
    let r2 = 99 :: Fp
    let commit2 = pointMul b $ commit crs p2 r2
    let addCommit = commit crs (polyAdd (polyScale a p1) (polyScale b p2)) (a*r1 + b*r2)
    return $ pointAdd commit1 commit2 == addCommit

