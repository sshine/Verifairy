
module CheckTest where

import Control.Monad
--import Data.Char (chr, isHexDigit)
--import Data.FileEmbed
--import Data.Foldable (for_)
import Data.Map (fromList)
--import qualified Data.Map as Map
import Data.Text (Text)
--import qualified Data.Text as Text
--import Data.Text.Read (hexadecimal)
--import Data.Void

import Hedgehog
import qualified Hedgehog.Gen
--import Test.Hspec
--import Test.Hspec.Megaparsec
import Test.Tasty.Hspec

import VerifPal.Types
import VerifPal.Check (process, ModelState(..), ModelError(..), ProcessingCounter, CanonExpr(..),CanonKnowledge(..), equationToList, equivalenceExpr, quicksort)
import Data.Map (Map)
import qualified Data.Map as Map

import Cases

shouldNotFail :: ModelState -> Expectation
shouldNotFail modelState =
  msErrors modelState `shouldBe` []

shouldFail :: ModelState -> Expectation
shouldFail modelState =
  msErrors modelState `shouldNotBe` []

spec_parsePrincipal :: Spec
spec_parsePrincipal = do
  describe "process" $ do
    it "validates data/alice1.vp" $
      process alice1modelast `shouldBe`
      ModelState {
          msPrincipalConstants = fromList [("Alice",fromList [(Constant {constantName = "a"},(Generates,3)),(Constant {constantName = "c0"},(Public,0)),(Constant {constantName = "c1"},(Public,1)),(Constant {constantName = "m1"},(Private,2)),              (Constant {constantName = "nil"},(Public,0))])],
          msProcessingCounter = 4,
          msConstants = fromList [
              (Constant {constantName = "a"},Generates),
              (Constant {constantName = "c0"},Public),
              (Constant {constantName = "c1"},Public),
              (Constant {constantName = "m1"},Private),
              (Constant {constantName = "nil"},Public)
          ], msErrors = [], msQueryResults = []}

shouldOverlapWith :: ModelState -> Constant -> Expectation
shouldOverlapWith modelState constant =
  msErrors modelState `shouldContain`
    [OverlappingConstant constant "can't generate the same thing twice"]

shouldMissConstant :: ModelState -> (Text, Text) -> Expectation
shouldMissConstant modelState (constantName, errorText) =
  -- TODO this way of testing for the Text of the missingconstant is not great.
  msErrors modelState `shouldContain`
    [MissingConstant (Constant constantName) errorText]

shouldHave :: ModelState -> (PrincipalName, [Constant]) -> IO ()
shouldHave modelState (principalName, constants) =
  case Map.lookup principalName (msPrincipalConstants modelState) of
    Nothing -> fail "Principal not found" -- True `shouldBe` False
    Just principalMap ->
      forM_ constants (\constant -> Map.member constant principalMap `shouldBe` True)

shouldHaveEquivalence :: ModelState -> [Text] -> Expectation
shouldHaveEquivalence modelState wantedConstants =
  msQueryResults modelState `shouldSatisfy` any predicate
  where
    predicate (Query (EquivalenceQuery actualConstants) _queryOptions, True) =
      actualConstants == map (\c -> Constant c) wantedConstants
    predicate _ = False

shouldHaveFresh :: ModelState -> Text -> Expectation
shouldHaveFresh modelState constant =
  msQueryResults modelState `shouldSatisfy` any isFresh
  where
    isFresh (Query (FreshnessQuery constant2) _queryOptions, True) =
      Constant constant == constant2
    isFresh _ = False

shouldHaveNotFresh :: ModelState -> Text -> Expectation
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

spec_equations :: Spec
spec_equations = do
  describe "equations" $ do
    let mkc name = CConstant (Constant {constantName=name}) CPublic
        a = mkc "a"
        b = mkc "b"
        c = mkc "c"
        g = mkc "G"
    it "equationToList [] = []" $ do
      equationToList [] a `shouldBe` [a]
    it "equationsToList G^a = [G a]" $ do
      equationToList [] (CG a) `shouldBe` [a]
    it "equationsToList (G^a)^b = [a,b]" $ do
      equationToList [] ((:^^:) (CG a) b) `shouldBe` [a,b]
    it "equationsToList (G^b)^a = [a,b]" $ do
      equationToList [] ((:^^:) (CG b) a) `shouldBe` [a,b]
    it "equationsToList (G^b)^(G^a) = [g,a,b]" $ do
      equationToList [] ((:^^:) (CG b) (CG a)) `shouldNotBe` [a,b]
      equationToList [] ((:^^:) (CG b) (CG a)) `shouldBe` [g,a,b]
    it "equationsToList G^a^G^b /= G^a^b" $ do
      let lhs = ((:^^:) (CG a) (CG b))
          rhs = ((:^^:) (CG a) b)
      equationToList [] lhs `shouldNotBe` equationToList [] rhs
    it "equationsToList ((G^a)^b)^c = [a,b,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG a) b) c) `shouldBe` [a,b,c]
    it "equationsToList ((G^b)^a)^c = [a,b,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG b) a) c) `shouldBe` [a,b,c]
    it "equationsToList ((G^c)^b)^a = [a,b,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG c) b) a) `shouldBe` [a,b,c]
    -- TODO should we typecheck that the innermost, leftmost expression
    -- always contains a G ?
    it "equationsToList ((G^c)^b)^(G^a) = [G^a,b,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG c) b) (CG a)) `shouldBe` [g,a,b,c]
    it "equationsToList ((G^c)^(G^b))^a = [G^b,a,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG c) (CG b)) a) `shouldBe` [g,a,b,c]
    it "equationsToList ((G^c)^(G^b))^(G^a) /= ((G^c)^b)^(G^a)" $ do
      equationToList [] ((:^^:) ((:^^:) (CG c) (CG b)) a
                        ) `shouldNotBe` equationToList [] (
                         (:^^:) ((:^^:) (CG c)     b) a)
      equationToList [] ((:^^:) ((:^^:) (CG c) (CG b)) (CG a)
                        ) `shouldNotBe` equationToList [] (
                         (:^^:) ((:^^:) (CG c) (CG b))     a)
    it "equationsToList ((G^c)^(G^b))^(G^a) = [G^a,G^b,c]" $ do
      equationToList [] ((:^^:) ((:^^:) (CG c) (CG b)) (CG a)) `shouldBe` [g,g,a,b,c]
    it "equationsToList (G^b_sk)^a_sk = [a_sk,b_sk]" $ do
      let dh1_ss_a = (:^^:) b_dh1_pk_a  a_dh1_sk
          dh1_ss_b = (:^^:) a_dh1_pk_b  b_dh1_sk
          pdk_a = CConstant (Constant {constantName = "pdk_a"}) CGenerates
          pdk_b = CConstant (Constant {constantName = "pdk_b"}) CGenerates
          b_dh1_sk = CConstant (Constant {constantName = "b_dh1_sk"}) CGenerates
          b_dh1_pk = CG b_dh1_sk
          b_t1_alpha = CPrimitive (ENC pdk_b b_dh1_pk) HasntQuestionMark
          a_t1_alpha = CPrimitive (ENC pdk_a a_dh1_pk) HasntQuestionMark
          a_dh1_pk_b = CPrimitive (DEC pdk_a a_t1_alpha) HasntQuestionMark
          b_dh1_pk_a = CPrimitive (DEC pdk_b b_t1_alpha) HasntQuestionMark
          a_dh1_sk = CConstant (Constant {constantName = "a_dh1_sk"}) CGenerates
          a_dh1_pk = CG a_dh1_sk
      equationToList [] ((:^^:) b_dh1_pk a_dh1_sk) `shouldBe` [a_dh1_sk, b_dh1_sk]
      equationToList [] ((:^^:) a_dh1_pk b_dh1_sk) `shouldBe` [a_dh1_sk, b_dh1_sk]
      equationToList [] dh1_ss_a `shouldBe` [a_dh1_sk, b_dh1_sk]
      equationToList [] dh1_ss_b `shouldBe` [a_dh1_sk, b_dh1_sk]
      equationToList [] dh1_ss_a `shouldBe` equationToList [] dh1_ss_b
      equivalenceExpr dh1_ss_a dh1_ss_b `shouldBe` True

spec_process :: Spec
spec_process = do
  describe "process" $ do
    it "validates data/alice1.vp" $ do
      let modelState = process alice1modelast
      modelState `shouldHave` ("Alice", Constant <$> ["a", "c0", "c1", "m1"])
      msConstants modelState `shouldBe`
        mkConstants [("a", Generates), ("c0", Public), ("c1", Public), ("m1", Private), ("nil", Public)]

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
      --- shouldNotFail modelState right now it fails due to confidentiality?
      modelState `shouldHave` ("A", Constant <$> ["x"])
      modelState `shouldHave` ("B", Constant <$> ["x"])

    it "rejects model with conflicting public/private knows" $
      process bad_publicprivate_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting generates/knows private" $
      process bad_generatesknows_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting knows private/knows password" $
      process bad_passwordprivate_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting knows public/knows private" $
      process bad_publicprivate_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting generates/knows private" $
      process bad_generatesknows_ast `shouldOverlapWith` Constant "x"

    it "rejects model with conflicting knows private/knows password" $
      process bad_passwordprivate_ast `shouldOverlapWith` Constant "x"

    it "rejects model with missing constant in confidentialityquery" $
      process bad_undefinedconstant_in_cfquery_ast `shouldMissConstant` ("y","TODO")

    it "rejects model that sends constant before it's defined" $ do
      let modelState = process bad_early_constant_ast
      modelState `shouldMissConstant`("yo","sender reference to unknown constant")

    it "rejects model that references undefined constant" $ do
      let modelState = process bad_assignment_to_undefined_ast
      shouldFail modelState
      modelState `shouldMissConstant` ("b","assignment to unbound constant")

spec_freshness :: Spec
spec_freshness = do
  describe "process" $ do
    it "checks simple freshness query" $ do
      let modelState = process freshness1model
      modelState `shouldHaveFresh` "x"
      modelState `shouldHaveNotFresh` "y"

    it "validates data/knows_freshness.vp" $ do
      let modelState = process knows_freshness_ast
      shouldNotFail modelState
      modelState `shouldHaveFresh` "a"

    it "validates data/freshness_aliased.vp" $ do
      let modelState = process freshness_aliased_ast
      shouldNotFail modelState
      modelState `shouldHaveFresh` "a"
      modelState `shouldHaveFresh` "b"
      modelState `shouldHaveFresh` "c"

    it "validates data/freshness_concat.vp" $ do
      let modelState = process freshness_concat_ast
      shouldNotFail modelState
      modelState `shouldHaveFresh` "b"
      modelState `shouldHaveFresh` "c"
      modelState `shouldHaveFresh` "d"

    it "rejects freshness query on (knows private)" $ do
      let modelState = process bad_knows_freshness_ast
      shouldNotFail modelState
      modelState `shouldHaveNotFresh` "a"

spec_equivalence :: Spec
spec_equivalence = do
  describe "process" $ do
    it "checks equivalence1 query" $ do
      let modelState = process equivalence1_ast
      shouldNotFail modelState
      modelState `shouldHaveEquivalence` ["msg", "from_a"]
    it "checks equivalence2 query" $ do
      let modelState = process equivalence2_ast
      shouldNotFail modelState
      modelState `shouldHaveEquivalence` ["a", "b_a"]
      modelState `shouldHaveEquivalence` ["b", "b_b"]
      modelState `shouldHaveEquivalence` ["c", "b_c"]
    it "checks equivalence3 query" $ do
      let modelState = process equivalence3_ast
      shouldNotFail modelState
      modelState `shouldHaveEquivalence` ["a", "b"]
      modelState `shouldHaveEquivalence` ["c", "d"]
    it "checks equivalence4 query" $ do
      let modelState = process equivalence4_ast
      shouldNotFail modelState
      modelState `shouldHaveEquivalence` ["dec_m1", "m1"]
      modelState `shouldHaveEquivalence` ["aead_dec_m1", "m1"]
      modelState `shouldHaveEquivalence` ["pk1", "dec_pk1"]
      modelState `shouldHaveEquivalence` ["pk2", "G_dec_m1"]
      modelState `shouldHaveEquivalence` ["pk2", "G_aead_dec_m1"]
      modelState `shouldHaveEquivalence` ["G_dec_m1", "G_aead_dec_m1"]

    let msEquivalence5 = process equivalence5_ast
    it "checks equivalence5: no errors" $ do
      shouldNotFail msEquivalence5

    it "checks equivalence5: a_dh1_pk, a_dh1_pk_b" $ do
      msEquivalence5 `shouldHaveEquivalence` ["a_dh1_pk", "a_dh1_pk_b"]

    it "checks equivalence5: b_dh1_pk, b_dh1_pk_a" $ do
      msEquivalence5 `shouldHaveEquivalence` ["b_dh1_pk", "b_dh1_pk_a"]

    it "checks equivalence5: dh1_ss_ab, dh1_ss_ba" $ do
      msEquivalence5 `shouldHaveEquivalence` ["dh1_ss_ab", "dh1_ss_ba"]

    it "checks equivalence5: dh1_ss_a, dh1_ss_b" $ do
      msEquivalence5 `shouldHaveEquivalence` ["dh1_ss_a", "dh1_ss_b"]

    it "checks equivalence5: dh1_ss_ab, dh1_ss_a" $ do
      msEquivalence5 `shouldHaveEquivalence` ["dh1_ss_ab", "dh1_ss_a"]

    it "checks equations2 queries" $ do
      let modelState = process equations2_ast
      shouldNotFail modelState
      -- TODO should NOT have: modelState `shouldHaveEquivalence` ["a", "b"]
      modelState `shouldHaveEquivalence` ["gyx", "gxy"]

hprop_yo :: Hedgehog.Property
hprop_yo =
  verifiedTermination $ property $ do
    ['a'] === ['a']
