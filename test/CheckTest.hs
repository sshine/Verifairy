
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
import VerifPal.Check (process, ModelState(..), emptyModelState, ModelError(..))

import Cases

shouldOverlapWith modelState constant =
  msErrors modelState `shouldContain` [OverlappingConstant constant]

spec_process :: Spec
spec_process = do
  describe "process" $ do
    it "validates data/alice1.vp" $
      process alice1modelast `shouldBe`
      ModelState {
          msConstants = Map.fromList [
              (Constant {constantName = "a"},Generates),
              (Constant {constantName = "c0"},Public),
              (Constant {constantName = "c1"},Public),
              (Constant {constantName = "m1"},Private)
          ], msErrors = []}

    it "rejects model with duplicates" $ do
      process dup1model `shouldOverlapWith` Constant "x"
      process dup2model `shouldOverlapWith` Constant "x"
      process dup3model `shouldOverlapWith` Constant "x"
      process dup4model `shouldOverlapWith` Constant "x"

    it "validates data/abknows.vp" $
      process abknowsast `shouldBe` emptyModelState

    it "rejects model with conflicting knows public/knows private" $
      process bad_publicprivate_ast `shouldBe` ModelState {
          msConstants = Map.fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"})]
      }

    it "rejects model with conflicting generates/knows private" $
      process bad_generatesknows_ast `shouldBe` ModelState {
          msConstants = Map.fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"})]
      }

    it "rejects model with conflicting knows private/knows password" $
      process bad_passwordprivate_ast `shouldBe` ModelState {
          msConstants = Map.fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"})]
      }
