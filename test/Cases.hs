{-# LANGUAGE TemplateHaskell #-}

module Cases where

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
import Data.List.NonEmpty

import VerifPal.Types
import VerifPal.Parser

mkc c = (:|) (Constant c) []

assertParseModel src =
  case parseModel src of
    Right model -> model

alice1 :: Text
alice1 = $(embedStringFile "data/alice1.vp")

alice1ast :: Principal
alice1ast = Principal{..}
  where
    principalName = "Alice"
    principalKnows =
      [ (cons (Constant "c0") (mkc "c1"), Public)
      , (mkc "m1", Private)
      , (mkc "a", Generates)
      ]

alice1model :: Text
alice1model = $(embedStringFile "data/alice1model.vp")

alice1modelast :: Model
alice1modelast = Model
  { modelAttacker = Active
  , modelParts = [ ModelPrincipal (Principal { principalName = "Alice", principalKnows = aliceKnows })]
  }
  where
    aliceKnows =
      [ (cons (Constant "c0") (mkc "c1"),Public)
      , (mkc "m1",Private)
      , (mkc "a",Generates)
      ]


bob1 :: Text
bob1 = $(embedStringFile "data/bob1.vp")

bob1ast :: Principal
bob1ast = Principal{..}
  where
    principalName = "Bob"
    principalKnows =
      [ (cons (Constant "c0") (mkc "c1"), Public)
      , (mkc "m2", Private)
      , (mkc "b", Generates)
      , (mkc "gb", Assignment (G (mkConst "b")))
      ]

equations1 :: Text
equations1 = $(embedStringFile "data/equations1.vp")

equations1ast :: Principal
equations1ast = Principal
  { principalName = "Server"
  , principalKnows =
      [ (mkc "x",Generates)
      , (mkc "y",Generates)
      , (mkc "gx",Assignment (G (EConstant (Constant {constantName = "x"}))))
      , (mkc "gy",Assignment (G (EConstant (Constant {constantName = "y"}))))
      , (mkc "gxy",Assignment ((:^:) (Constant {constantName = "gx"}) (EConstant (Constant {constantName = "y"}))))
      , (mkc "gyx",Assignment ((:^:) (Constant {constantName = "gy"}) (EConstant (Constant {constantName = "x"}))))
      ]
  }

equations2 :: Text
equations2 = $(embedStringFile "data/equations2.vp")
equations2_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "Server", principalKnows = [
                                                                                             (mkc "x",Generates),
                                                                                             (mkc "y",Generates),
                                                                                             (mkc "gx",Assignment (G (EConstant (Constant {constantName = "x"})))),
                                                                                             (mkc "gy",Assignment (G (EConstant (Constant {constantName = "y"})))),
                                                                                             (mkc "gxy",Assignment ((:^:) (Constant {constantName = "gx"}) (EConstant (Constant {constantName = "y"})))),
                                                                                             (mkc "gyx",Assignment ((:^:) (Constant {constantName = "gy"}) (EConstant (Constant {constantName = "x"}))))]}),ModelQueries [Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "gx"},Constant {constantName = "gy"}]}, queryOptions = Nothing},Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "gyx"},Constant {constantName = "gxy"}]}, queryOptions = Nothing}]]}

bob1model :: Text
bob1model = $(embedStringFile "data/bob1model.vp")

bob1modelast :: Model
bob1modelast = Model
  { modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "Bob", principalKnows = bobKnows })] }
  where
    bobKnows =
      [ (cons (Constant "c0") (mkc "c1"),Public)
      , (mkc "m2",Private)
      , (mkc "b",Generates)
      , (mkc "gb",Assignment (G (EConstant (Constant {constantName = "b"}))))
      ]

simple1 :: Text
simple1 = $(embedStringFile "data/simple1.vp")

simple1ast :: Model
simple1ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "a",Generates),(mkc "ga",Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ga"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(mkc"m1",Private),(mkc "b",Generates),(mkc "gb",Assignment (G (EConstant (Constant {constantName = "b"})))),(mkc "ss_a",Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"})))),(mkc "e1",Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "gb"},False),(Constant {constantName = "e1"},False)]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc"ss_b",Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"})))),(mkc "e1_dec",Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark))]})]}

simple1_complete_active :: Text
simple1_complete_active = $(embedStringFile "data/simple1_complete_active.vp")

simple1_complete_active_ast :: Model
simple1_complete_active_ast = assertParseModel simple1_complete_active

confidentiality1 :: Text
confidentiality1 = $(embedStringFile "data/confidentiality1.vp")
confidentiality1_ast :: Model
confidentiality1_ast = assertParseModel confidentiality1

confidentiality2 :: Text
confidentiality2 = $(embedStringFile "data/confidentiality2.vp")
confidentiality2_ast :: Model
confidentiality2_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "x",Private),(mkc "z",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "x"})]) HasntQuestionMark)),(mkc "z",Leaks),(mkc "a",Private),(mkc "b",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),(mkc "a",Leaks)]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "x"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "z"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "a"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "b"}}, queryOptions = Nothing}]]}

confidentiality3 :: Text
confidentiality3 = $(embedStringFile "data/confidentiality3.vp")
confidentiality3_ast :: Model
confidentiality3_ast = assertParseModel confidentiality3

simple1_complete_passive :: Text
simple1_complete_passive = $(embedStringFile "data/simple1_complete_passive.vp")

simple1_complete_passive_ast :: Model
simple1_complete_passive_ast = Model Passive []

simple2 :: Text
simple2 = $(embedStringFile "data/simple2.vp")

simple2ast :: Model
simple2ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "a",Generates),(mkc "ga",Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ga"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(mkc "m1",Private),(mkc "b",Generates),(mkc "gb",Assignment (G (EConstant (Constant {constantName = "b"})))),(mkc "ss_a",Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"})))),(mkc "e1",Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "gb"},False),(Constant {constantName = "e1"},False)]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "ss_b",Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"})))),(mkc "e1_dec",Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark))]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "e1"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "m1"}}, queryOptions = Nothing},Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "e1"},False)]}}, queryOptions = Nothing},Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "ss_a"},Constant {constantName = "ss_b"}]}, queryOptions = Nothing}]]}

message1 :: Text
message1 = $(embedStringFile "data/message1.vp")

message1ast :: Message
message1ast = Message "Alice" "Bob" [(Constant "x", False)]

phase1 :: Text
phase1 = $(embedStringFile "data/phase1.vp")

phase1ast :: Phase
phase1ast = Phase 42

freshness1 :: Text
freshness1 = $(embedStringFile "data/freshness1.vp")
freshness1ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "a",Private),(mkc "b",Generates),(mkc "ha",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),(mkc "hb",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ha"},False),(Constant {constantName = "hb"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(mkc "a",Private),(mkc "_",Assignment (EPrimitive (ASSERT (EConstant (Constant {constantName = "ha"})) (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)) HasntQuestionMark))]}),ModelQueries [Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "ha"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "hb"}}, queryOptions = Nothing}]]}
freshness1model :: Model
freshness1model = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "x",Generates),(mkc "y",Private)]}),ModelQueries [Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "x"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "y"}}, queryOptions = Nothing}]]}

freshness2 :: Text
freshness2 = $(embedStringFile "data/freshness2.vp")

freshness2ast :: Model
freshness2ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(mkc "a",Private),(mkc "b",Generates),(mkc "ha",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),(mkc "hb",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ha"},False),(Constant {constantName = "hb"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(mkc "a",Private),(mkc "_",Assignment (EPrimitive (ASSERT (EConstant (Constant {constantName = "ha"})) (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)) HasntQuestionMark))]}),ModelQueries [Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "ha"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "hb"}}, queryOptions = Nothing}]]}

freshness3 :: Text
freshness3 = $(embedStringFile "data/freshness3.vp")
freshness3_ast :: Model
freshness3_ast = assertParseModel freshness3

freshness_concat :: Text
freshness_concat = $(embedStringFile "data/freshness_concat.vp")
freshness_concat_ast :: Model
freshness_concat_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "a",Generates),(mkc "b",Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),(mkc "c",Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark)),(mkc "d",Assignment (EPrimitive (CONCAT [EConstant (Constant {constantName = "c"})]) HasntQuestionMark))]}),ModelQueries [Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "b"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "c"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "d"}}, queryOptions = Nothing}]]}

equivalence1 :: Text
equivalence1 = $(embedStringFile "data/equivalence1.vp")
equivalence1_ast = Model {
  modelAttacker = Passive,
  modelParts = [
      ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "msg",Private),(mkc "key",Private),(mkc "encrypted",Assignment (EPrimitive (ENC (EConstant (Constant {constantName = "key"})) (EConstant (Constant {constantName = "msg"}))) HasntQuestionMark))]}),
      ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "key",Private)]}),ModelMessage (Message {messageSender = "A", messageReceiver = "B", messageConstants = [(Constant {constantName = "encrypted"},False)]}),
      ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "from_a",Assignment (EPrimitive (DEC (EConstant (Constant {constantName = "key"})) (EConstant (Constant {constantName = "encrypted"}))) HasntQuestionMark))]}),
      ModelQueries [Query {queryKind = EquivalenceQuery {equivalenceConstants = [
          Constant {constantName = "msg"},
          Constant {constantName = "from_a"}]}, queryOptions = Nothing}]]}

equivalence2 :: Text
equivalence2 = $(embedStringFile "data/equivalence2.vp")
equivalence2_ast = assertParseModel equivalence2

equivalence3 :: Text
equivalence3 = $(embedStringFile "data/equivalence3.vp")
equivalence3_ast = assertParseModel equivalence3

equivalence4 :: Text
equivalence4 = $(embedStringFile "data/equivalence4.vp")
equivalence4_ast = assertParseModel equivalence4

equivalence5 :: Text
equivalence5 = $(embedStringFile "data/equivalence5.vp")
equivalence5_ast = assertParseModel equivalence5

abknows :: Text
abknows = $(embedStringFile "data/abknows.vp")

abknowsast :: Model
abknowsast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "x",Private)]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "x"}}, queryOptions = Nothing}]] }

bad_publicprivate :: Text
bad_publicprivate = $(embedStringFile "data/bad_publicprivate.vp")

bad_publicprivate_ast :: Model
bad_publicprivate_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "x",Public)]})]}

bad_passwordprivate :: Text
bad_passwordprivate = $(embedStringFile "data/bad_passwordprivate.vp")

bad_passwordprivate_ast :: Model
bad_passwordprivate_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "x",Password)]})]}

bad_generatesknows :: Text
bad_generatesknows = $(embedStringFile "data/bad_generatesknows.vp")

bad_generatesknows_ast :: Model
bad_generatesknows_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(mkc "x",Generates)]})]}

bad_undefinedconstant_in_cfquery :: Text
bad_undefinedconstant_in_cfquery = $(embedStringFile "data/bad_undefinedconstant_in_cfquery.vp")
bad_undefinedconstant_in_cfquery_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "y"}}, queryOptions = Nothing}]]}

bad_early_constant :: Text
bad_early_constant = $(embedStringFile "data/bad_early_constant.vp")
bad_early_constant_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = []}),ModelPrincipal (Principal {principalName = "B", principalKnows = []}),ModelMessage (Message {messageSender = "A", messageReceiver = "B", messageConstants = [(Constant {constantName = "yo"},False)]}),ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "yo",Private)]})]}

model_concat :: Text
model_concat = $(embedStringFile "data/concat.vp")
model_concat_ast = Model {
  modelAttacker = Passive,
    modelParts = [
      ModelPrincipal (
          Principal {
              principalName = "A",
                principalKnows = [
                  (mkc "a",Private),
                  (mkc "b",Private),
                  (mkc "c",
                    Assignment (
                      EPrimitive (
                          CONCAT [
                              EConstant (Constant {constantName = "a"}),
                              EConstant (Constant {constantName = "b"})]                                                       ) HasntQuestionMark))
                  ]
              })]}

bad_knows_freshness :: Text
bad_knows_freshness = $(embedStringFile "data/bad_knows_freshness.vp")
bad_knows_freshness_ast = Model {
  modelAttacker = Passive,
  modelParts = [
    ModelPrincipal (
        Principal {
            principalName = "A",
            principalKnows = [
                  (mkc "a",Private)
              ]
          }),
   ModelQueries [ Query {
                    queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "a"}},
                    queryOptions=Nothing
                    }]
   ]}

knows_freshness :: Text
knows_freshness = $(embedStringFile "data/knows_freshness.vp")
knows_freshness_ast :: Model
knows_freshness_ast = assertParseModel knows_freshness

freshness_aliased :: Text
freshness_aliased = $(embedStringFile "data/freshness_aliased.vp")
freshness_aliased_ast :: Model
freshness_aliased_ast = assertParseModel freshness_aliased


-- Negative cases

dup1model, dup2model, dup3model, dup4model :: Model
dup1model = Model Passive [mp "Alice" [privx, privx]]
dup2model = Model Passive [mp "Alice" [privx, pubx]]
dup3model = Model Passive [mp "Alice" [privx], mp "Bob" [privx]]
dup4model = Model Passive [mp "Alice" [privx], mp "Bob" [pubx]]

mp name knows = ModelPrincipal (Principal name knows)
privx = (mkc "x", Private)
pubx = (mkc "x", Public)

------------------------------------------------------------------------------

challengeResponse :: Text
challengeResponse = $(embedStringFile "foreign_models/verifpal/test/challengeresponse.vp")

challengeResponseModel :: Model
challengeResponseModel = assertParseModel challengeResponse

foreignRingSign :: Text
foreignRingSign = $(embedStringFile "foreign_models/verifpal/test/ringsign.vp")

foreignRingSignModel :: Model
foreignRingSignModel = assertParseModel foreignRingSign

-- principal A[generates a; c = b ]
-- this should give an error that "b" is unbound
bad_assignment_to_undefined_ast = Model {
  modelAttacker = Passive,
  modelParts = [
    ModelPrincipal (
        Principal {
            principalName = "A",
            principalKnows = [
                  (mkc "a",Generates),
                  (mkc "c",Assignment (G (EConstant (Constant {constantName = "b"}))))
              ]
          })]}

duplicateModel :: Model
duplicateModel = Model
  { modelAttacker = Passive
  , modelParts =
      [ ModelPrincipal (Principal "Alice" aliceKnows)
      , ModelPrincipal (Principal "Bob" bobKnows)
      ]
  }
  where
    aliceKnows =
      [ (mkc "x" , Private)
      , (mkc "x", Private)
      ]
    bobKnows = []
