
module CheckTest where

import Control.Monad
import Data.Char (chr, isHexDigit)
import Data.FileEmbed
import Data.Foldable (for_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Read (hexadecimal)
import Data.Void

import Hedgehog
import Test.Hspec
import Test.Hspec.Megaparsec
import Test.Tasty.Hspec

import VerifPal.Types
import VerifPal.Check (process', ModelState(..), emptyModelState)

import Cases

spec_parsePrincipal :: Spec
spec_parsePrincipal = do
  describe "process'" $ do
    it "validates data/alice1.vp" $
      process' alice1modelast `shouldBe` emptyModelState

    it "rejects model with duplicates" $
      process' alice1modelast `shouldBe` emptyModelState

