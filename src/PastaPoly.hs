{- |
Copyright: (c) 2022 Eric Schorn
SPDX-License-Identifier: MIT
Maintainer: Eric Schorn <eric.schorn@nccgroup.com>

haskell polynomial stuff
-}

module PastaPoly
       ( someFunc
       ) where

import PastaCurves

someFunc :: IO ()
someFunc = do
       print "Sample executable for pasta-curves"
       print $ pointMul (2 ^ (200::Integer) - 1 :: Fq) (base :: Pallas)
