module Fft (module Fft) where

import PastaCurves
import Poly --(Polynomial (Coefficients))
--import Poly

--x = 9 :: Fp


fft2 :: Field a => [a] -> [a] -> [a]
fft2 vals domain 
  | length vals == 1 = vals
  | otherwise = result
  where
    left = fft2 ((vals !!) <$> [0,2..length vals-1]) ((domain !!) <$> [0,2..length domain-1])
    right = fft2 (fmap (vals !!) [1,3..length vals-1]) (fmap (domain !!) [0,2..length domain-1])
    xyz = zip3 left right domain
    oi1 = [x + y*z | (x,y,z) <- xyz]
    oi2 = [x - y*z | (x,y,z) <- xyz]
    result = oi1 ++ oi2 



-- hi :: Integer -> Integer
-- hi a = a * a

-- hi :: Int -> Int
-- hi a = a + a



--fft :: [Fp] -> [Fp] -> [Fp] -> [Fp]
fft :: [Integer] -> Integer -> [Integer] -> [Integer]
fft vals modulus domain 
  | length vals == 1 = vals
  | otherwise = result
  where
    left = fft (fmap (vals !!) [0,2..length vals-1]) modulus (fmap (domain !!) [0,2..length domain-1])
    right = fft (fmap (vals !!) [1,3..length vals-1]) modulus (fmap (domain !!) [0,2..length domain-1])
    xyz = zip3 left right domain
    oi1 = [(x + y*z) `mod` modulus | (x,y,z) <- xyz]
    oi2 = [(x - y*z) `mod` modulus | (x,y,z) <- xyz]
    result = oi1 ++ oi2 


-- def inverse_fft(vals, modulus, domain):
--     vals = fft(vals, modulus, domain)
--     return [x * modular_inverse(len(vals), modulus) % modulus for x in [vals[0]] + vals[1:][::-1]]

ifft2 :: Field a => [a] -> [a] -> [a]
ifft2 vals domain = result
  where
    vv = fft2 vals  domain
    result = [x * inv0 (fromInteger (toInteger (length vv))) | x <- head vv : reverse (tail vv)]
 


vals = [3, 1, 4, 1, 5, 9, 2, 6]
nn = 337
dd = [1, 85, 148, 111, 336, 252, 189, 226]  -- TODO: Weird, it doesn't depend on the last element!!!
-- dd = [148, 111, 336, 252, 189, 226, 1, 85]  -- TODO: Weird, it doesn't depend on the last element!!!

mix = fft vals nn dd
-- should be [31, 70, 109, 74, 334, 181, 232, 4]

pp = [31, 70, 109, 74, 334, 181, 232, 4]

--polyEval pt c = foldr (\a b -> a + b * pt) 0 c

getDomain = result
  where
    --x = 5 :: Fp  -- a non square
    order = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 `div` 2^32
    can = head [((fromInteger x::Fp) ^ order) ^ (2^28) | x <- [2..], ((fromInteger x::Fp) ^ order) ^ (2^31) /= 1] -- x=5
    result = [can^i | i <- [0..15]]

dom = getDomain
iff = ifft2 [1,2,3,4,5,6,7,8::Fp] dom
ff = fft2 iff dom


gimme16Samples :: Polynomial Fp -> [Fp] -> [Fp]
gimme16Samples poly domain = result
  where
    result = fmap (polyEval poly) domain

mul16 :: [Fp] -> [Fp] -> [Fp]
mul16 = zipWith (*)


checkMe a b = (polyMul a b,
                                 polyNew (ifft2 (mul16 (gimme16Samples a getDomain) (gimme16Samples b getDomain)) getDomain))


{-

TO DO
 -- read; understand why right side of dd is don't-care
 -- get it working for an example Fp; what is correct domain (a list comprehension)
 -- get a quickcheck test working
 -- see https://crypto.stackexchange.com/questions/63614/finding-the-n-th-root-of-unity-in-a-finite-field

so Fermat says a^{p-1} = 1 mod p
we know p-1 can be written as q*2^s (where s = 32, q = 0x40000000000000000000000000000000224698fc094cf91b992d30ed)
and euler criterion a^{(p-1)/2} = 1 (for square)
so any number raised to q will be in a multiplicative group of order 2^32
-}


-- def fft(vals, modulus, domain):
--     if len(vals) == 1:
--         return vals
--     L = fft(vals[::2], modulus, domain[::2])
--     R = fft(vals[1::2], modulus, domain[::2])
--     o = [0 for i in vals]
--     for i, (x, y) in enumerate(zip(L, R)):
--         y_times_root = y*domain[i]
--         o[i] = (x+y_times_root) % modulus
--         o[i+len(L)] = (x-y_times_root) % modulus
--     return o






