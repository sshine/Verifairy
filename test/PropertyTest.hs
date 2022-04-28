{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Foldable
import Data.Traversable
import Data.Void
import Hedgehog
import Hedgehog.Main
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen
import Debug.Trace (traceM)

tests :: IO Bool
tests =
  checkParallel $ Group "Test.Example" [
      ("prop_reverse", prop_reverse)
    ]

myreverse val = reverse val

prop_reverse :: Property
prop_reverse =
  property $ do
    xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
    annotateShow ("her er min annotation", length xs)
    traceM "test test"
    reverse (myreverse xs) === xs


myA :: Maybe Int
myA = do
  traceM "a"
  pure 5

main :: IO ()
main = do
  traceM "test"
  defaultMain [tests]
  traverse_ print myA
  traceM "test2"
