{-# LANGUAGE OverloadedStrings #-}

module PropTest where

import Data.Foldable
import Data.Traversable
import Data.Void
import Hedgehog
import Hedgehog.Main
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen
import Debug.Trace (traceM)

hprop_reverse :: Property
hprop_reverse =
  property $ do
    xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
    annotateShow ("her er min annotation", length xs)
    traceM "test test"
    reverse (reverse xs) === xs
