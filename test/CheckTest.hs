
module CheckTest where

import Control.Monad
import Data.Char (chr, isHexDigit)
import Data.FileEmbed
import Data.Foldable (for_)
import Data.Map (fromList)
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
import VerifPal.Check (process, ModelState(..), emptyModelState, ModelError(..), ProcessingCounter)
import VerifPal.Parser
import Data.Map (Map)
import qualified Data.Map as Map

import Cases

shouldNotFail modelState =
  msErrors modelState `shouldBe` []

spec_parsePrincipal :: Spec
spec_parsePrincipal = do
  describe "process" $ do
    it "validates data/alice1.vp" $
      process alice1modelast `shouldBe`
      ModelState {
          msPrincipalConstants = fromList [("Alice",fromList [(Constant {constantName = "a"},(Generates,3)),(Constant {constantName = "c0"},(Public,0)),(Constant {constantName = "c1"},(Public,1)),(Constant {constantName = "m1"},(Private,2))])],
          msProcessingCounter = 4,
          msConstants = fromList [
              (Constant {constantName = "a"},Generates),
              (Constant {constantName = "c0"},Public),
              (Constant {constantName = "c1"},Public),
              (Constant {constantName = "m1"},Private)
          ], msErrors = [], msQueryResults = []}

shouldOverlapWith modelState constant =
  msErrors modelState `shouldContain`
    [OverlappingConstant constant "can't generate the same thing twice"]

shouldHave modelState (principalName, constants) =
  case Map.lookup principalName (msPrincipalConstants modelState) of
    Nothing -> fail "Principal not found" -- True `shouldBe` False
    Just principalMap ->
      forM_ constants (\constant -> Map.member constant principalMap `shouldBe` True)

shouldHaveFresh modelState constant =
  msQueryResults modelState `shouldSatisfy` any isFresh
  where
    isFresh (Query (FreshnessQuery constant2) _queryOptions, True) =
      Constant constant == constant2
    isFresh _ = False

shouldHaveNotFresh modelState constant =
  msQueryResults modelState `shouldSatisfy` any isNotFresh
  where
    isNotFresh (Query (FreshnessQuery constant2) _queryOptions, False) =
      Constant constant == constant2
    isNotFresh _ = False

mkModelState :: [(Text, Knowledge)] -> ModelState
mkModelState constants = ModelState
  { msConstants = mkConstants constants
  , msPrincipalConstants = Map.empty
  , msProcessingCounter = 0
  , msQueryResults = []
  , msErrors = []
  }

mkConstants :: [(Text, Knowledge)] -> Map Constant Knowledge
mkConstants constants =
  Map.fromList [ (Constant name, knowledge) | (name, knowledge) <- constants ]

mkPrincipalMap:: [(Text, Knowledge, ProcessingCounter)] -> Map Constant (Knowledge, ProcessingCounter)
mkPrincipalMap constants = Map.fromList
  [ (Constant name, (knowledge, count)) | (name, knowledge, count) <- constants ]

spec_process :: Spec
spec_process = do
  describe "process" $ do
    it "validates data/alice1.vp" $ do
      let modelState = process alice1modelast
      modelState `shouldHave` ("Alice", Constant <$> ["a", "c0", "c1", "m1"])
      msConstants modelState `shouldBe`
        mkConstants [("a", Generates), ("c0", Public), ("c1", Public), ("m1", Private)]

    it "rejects model with duplicates 1" $ do
      shouldNotFail (process dup1model)

    it "rejects model with duplicates 2" $ do
      process dup2model `shouldOverlapWith` Constant "x"

    it "rejects model with duplicates 3" $ do
      shouldNotFail (process dup3model)

    it "rejects model with duplicates 4" $ do
      process dup4model `shouldOverlapWith` Constant "x"

    it "validates data/abknows.vp" $ do
      let modelState = process abknowsast
      modelState `shouldHave` ("A", Constant <$> ["x"])
      modelState `shouldHave` ("B", Constant <$> ["x"])
      msConstants modelState `shouldBe` mkConstants [("x", Private)]

    it "rejects model with conflicting public/private knows" $
      process bad_publicprivate_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting generates/knows private" $
      process bad_generatesknows_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting knows private/knows password" $
      process bad_passwordprivate_ast `shouldOverlapWith` Constant "x"

    it "validates data/abknows.vp" $
      process abknowsast `shouldBe` ModelState {msConstants = fromList [(Constant {constantName = "x"},Private)], msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "x"},(Private,0))]),("B",fromList [(Constant {constantName = "x"},(Private,1))])],
          msProcessingCounter = 2, msQueryResults = [], msErrors = [NotImplemented "confidentiality query not implemented"]}

    it "validates data/knows_freshness.vp" $
      process knows_freshness_ast `shouldBe` ModelState {
      msConstants = fromList [(Constant {constantName = "a"},Generates)]
        , msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "a"},(Generates,0))])],
          msProcessingCounter = 1,
          msQueryResults = [
            (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "a"}}, queryOptions = Nothing},
             True -- <-- query satisfied, this is fresh
            )
            ], msErrors = []}

    it "validates data/freshness_aliased.vp" $
      process freshness_aliased_ast `shouldBe` ModelState {
      msConstants = fromList [(Constant {constantName = "a"},Generates),(Constant {constantName = "b"},Assignment (EConstant (Constant {constantName = "a"}))),(Constant {constantName = "c"},Assignment (EConstant (Constant {constantName = "b"})))], msErrors = [],
      msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "a"},(Generates,0)),(Constant {constantName = "b"},(Assignment (EConstant (Constant {constantName = "a"})),1)),(Constant {constantName = "c"},(Assignment (EConstant (Constant {constantName = "b"})),3))])],
        msProcessingCounter = 5,
        msQueryResults = [
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "a"}}, queryOptions = Nothing},True),
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "b"}}, queryOptions = Nothing},True),
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "c"}}, queryOptions = Nothing},True)
                           ]}

    it "validates data/freshness_concat.vp" $
      process freshness_concat_ast `shouldBe` ModelState {
      msConstants = fromList [
          (Constant {constantName = "a"},Generates),
          (Constant {constantName = "b"},Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),
          (Constant {constantName = "c"},Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark)),
          (Constant {constantName = "d"},Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "c"})]) HasntQuestionMark))],
      msPrincipalConstants = fromList [
          ("A",fromList [(Constant {constantName = "a"},(Generates,0)),
                         (Constant {constantName = "b"},(Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "a"})]) HasntQuestionMark),1)),
                         (Constant {constantName = "c"},(Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark),3)),
                         (Constant {constantName = "d"},(Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "c"})]) HasntQuestionMark),5))])
          ],
      msProcessingCounter = 7, msErrors = [],
      msQueryResults = [
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "b"}}, queryOptions = Nothing},True),
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "c"}}, queryOptions = Nothing},True),
          (Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "d"}}, queryOptions = Nothing},True)
      ]}

    it "rejects model with conflicting knows public/knows private" $
      process bad_publicprivate_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"}) "can't generate the same thing twice"],
          msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "x"},(Private,0))])],
          msProcessingCounter = 1,
          msQueryResults = []
      }

    it "rejects model with conflicting generates/knows private" $
      process bad_generatesknows_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"}) "can't generate the same thing twice"],
          msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "x"},(Private,0))])],
          msProcessingCounter = 1,
          msQueryResults = []
      }
    it "rejects model with conflicting knows private/knows password" $
      process bad_passwordprivate_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "x"},Private)],
          msErrors = [OverlappingConstant (Constant {constantName = "x"}) "can't generate the same thing twice"],
          msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "x"},(Private,0))])],
          msProcessingCounter = 1,
          msQueryResults = []
          }
    it "rejects model with missing constant in confidentialityquery" $
      process bad_undefinedconstant_in_cfquery_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "x"},Private)],
          msErrors = [MissingConstant (Constant {constantName = "y"}) "TODO"],
          msPrincipalConstants = Map.empty,
          msProcessingCounter = 1,
          msQueryResults = []
      }
    it "rejects model that sends constant before it's defined" $
      process bad_early_constant_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "yo"},Private)],
          msErrors = [MissingConstant (Constant {constantName = "yo"}) "sender reference to unknown constant"],
          msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "yo"},(Private,1))])],
          msProcessingCounter = 2,
          msQueryResults = []
      }
    it "rejects model that that checks for freshness on (knows private)" $
      process bad_knows_freshness_ast `shouldBe` ModelState {
          msConstants = fromList [(Constant {constantName = "a"},Private)],
          msPrincipalConstants = fromList [("A",fromList [(Constant {constantName = "a"},(Private,0))])],
          msProcessingCounter = 1,
          msErrors = [],
          msQueryResults = [(Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "a"}}, queryOptions = Nothing},
                             False -- <- query failed!
                            )]
      }

    it "rejects model that references undefined constant" $
      process bad_assignment_to_undefined_ast `shouldBe`  ModelState {
      msConstants = fromList [
          (Constant {constantName = "a"},
           Generates),
          (Constant {constantName = "c"}, Assignment (EConstant ( Constant {constantName = "b"})))
      ],
      msErrors = [MissingConstant (Constant{constantName="b"}) "assignment to unbound constant"],
      msProcessingCounter = 3,
      msPrincipalConstants = fromList [
          ("A",fromList [
              (Constant {constantName = "a"},(Generates,0)),
                (Constant {constantName = "c"},(Assignment (EConstant (Constant {constantName = "b"})),1))
              ])
          ],
      msQueryResults = []
      }


spec_freshness :: Spec
spec_freshness = do
  describe "process" $ do
    it "checks simple freshness query" $ do
      let modelState = process freshness1model
      modelState `shouldHaveFresh` "x"
      modelState `shouldHaveNotFresh` "y"

