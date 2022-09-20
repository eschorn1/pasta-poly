module Main (main) where

import System.Environment (setEnv)
import Test.Tasty (defaultMain, testGroup)
import TestPoly

main :: IO ()
main = do
  setEnv "TASTY_QUICKCHECK_TESTS" "10_000"
  defaultMain $ testGroup "\nRunning Tests" [firstPoly, firstPoly2]
  print "Finished!"