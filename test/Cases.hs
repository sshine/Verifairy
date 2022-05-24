{-# LANGUAGE TemplateHaskell #-}

module Cases where

import Control.Monad()
--import Data.Char (chr, isHexDigit)
import Data.FileEmbed
--import Data.Foldable (for_)
import Data.Map ()
--import qualified Data.Map as Map
import Data.Text (Text)
--import qualified Data.Text as Text
--import Data.Text.Read (hexadecimal)
import Data.Void()
import Data.List.NonEmpty

import VerifPal.Types
import VerifPal.Parser

mkc :: Text -> NonEmpty Constant
mkc c = (:|) (Constant c) []

assertParseModel :: Text -> Model
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
equations2_ast :: Model
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

confidentiality4 :: Text
confidentiality4 = $(embedStringFile "data/confidentiality4.vp")
confidentiality4_ast :: Model
confidentiality4_ast = assertParseModel confidentiality4

confidentiality5 :: Text
confidentiality5 = $(embedStringFile "data/confidentiality5.vp")
confidentiality5_ast :: Model
confidentiality5_ast = assertParseModel confidentiality5

confidentiality6 :: Text
confidentiality6 = $(embedStringFile "data/confidentiality6.vp")
confidentiality6_ast :: Model
confidentiality6_ast = assertParseModel confidentiality6

confidentiality7 :: Text
confidentiality7 = $(embedStringFile "data/confidentiality7.vp")
confidentiality7_ast :: Model
confidentiality7_ast = assertParseModel confidentiality7

confidentiality8 :: Text
confidentiality8 = $(embedStringFile "data/confidentiality8.vp")
confidentiality8_ast :: Model
confidentiality8_ast = assertParseModel confidentiality8

confidentiality9 :: Text
confidentiality9 = $(embedStringFile "data/confidentiality9.vp")
confidentiality9_ast :: Model
confidentiality9_ast = assertParseModel confidentiality9

confidentiality10 :: Text
confidentiality10 = $(embedStringFile "data/confidentiality10.vp")
confidentiality10_ast :: Model
confidentiality10_ast = assertParseModel confidentiality10

confidentiality11 :: Text
confidentiality11 = $(embedStringFile "data/confidentiality11.vp")
confidentiality11_ast :: Model
confidentiality11_ast = assertParseModel confidentiality11

confidentiality12 :: Text
confidentiality12 = $(embedStringFile "data/confidentiality12.vp")
confidentiality12_ast :: Model
confidentiality12_ast = assertParseModel confidentiality12

confidentiality13 :: Text
confidentiality13 = $(embedStringFile "data/confidentiality13.vp")
confidentiality13_ast :: Model
confidentiality13_ast = assertParseModel confidentiality13

confidentiality14 :: Text
confidentiality14 = $(embedStringFile "data/confidentiality14.vp")
confidentiality14_ast :: Model
confidentiality14_ast = assertParseModel confidentiality14

confidentiality15 :: Text
confidentiality15 = $(embedStringFile "data/confidentiality15.vp")
confidentiality15_ast :: Model
confidentiality15_ast = assertParseModel confidentiality15

confidentiality16 :: Text
confidentiality16 = $(embedStringFile "data/confidentiality16.vp")
confidentiality16_ast :: Model
confidentiality16_ast = assertParseModel confidentiality16

confidentiality17 :: Text
confidentiality17 = $(embedStringFile "data/confidentiality17.vp")
confidentiality17_ast :: Model
confidentiality17_ast = assertParseModel confidentiality17

confidentiality18 :: Text
confidentiality18 = $(embedStringFile "data/confidentiality18.vp")
confidentiality18_ast :: Model
confidentiality18_ast = assertParseModel confidentiality18

confidentiality19 :: Text
confidentiality19 = $(embedStringFile "data/confidentiality19.vp")
confidentiality19_ast :: Model
confidentiality19_ast = assertParseModel confidentiality19

confidentiality20 :: Text
confidentiality20 = $(embedStringFile "data/confidentiality20.vp")
confidentiality20_ast :: Model
confidentiality20_ast = assertParseModel confidentiality20

confidentiality21 :: Text
confidentiality21 = $(embedStringFile "data/confidentiality21.vp")
confidentiality21_ast :: Model
confidentiality21_ast = assertParseModel confidentiality21

confidentiality22 :: Text
confidentiality22 = $(embedStringFile "data/confidentiality22.vp")
confidentiality22_ast :: Model
confidentiality22_ast = assertParseModel confidentiality22

confidentiality23 :: Text
confidentiality23 = $(embedStringFile "data/confidentiality23.vp")
confidentiality23_ast :: Model
confidentiality23_ast = assertParseModel confidentiality23

confidentiality24 :: Text
confidentiality24 = $(embedStringFile "data/confidentiality24.vp")
confidentiality24_ast :: Model
confidentiality24_ast = assertParseModel confidentiality24

confidentiality25 :: Text
confidentiality25 = $(embedStringFile "data/confidentiality25.vp")
confidentiality25_ast :: Model
confidentiality25_ast = assertParseModel confidentiality25

confidentiality26 :: Text
confidentiality26 = $(embedStringFile "data/confidentiality26.vp")
confidentiality26_ast :: Model
confidentiality26_ast = assertParseModel confidentiality26

confidentiality27 :: Text
confidentiality27 = $(embedStringFile "data/confidentiality27.vp")
confidentiality27_ast :: Model
confidentiality27_ast = assertParseModel confidentiality27

confidentiality28 :: Text
confidentiality28 = $(embedStringFile "data/confidentiality28.vp")
confidentiality28_ast :: Model
confidentiality28_ast = assertParseModel confidentiality28

confidentiality29 :: Text
confidentiality29 = $(embedStringFile "data/confidentiality29.vp")
confidentiality29_ast :: Model
confidentiality29_ast = assertParseModel confidentiality29

confidentiality30 :: Text
confidentiality30 = $(embedStringFile "data/confidentiality30.vp")
confidentiality30_ast :: Model
confidentiality30_ast = assertParseModel confidentiality30

confidentiality31 :: Text
confidentiality31 = $(embedStringFile "data/confidentiality31.vp")
confidentiality31_ast :: Model
confidentiality31_ast = assertParseModel confidentiality31

confidentiality32 :: Text
confidentiality32 = $(embedStringFile "data/confidentiality32.vp")
confidentiality32_ast :: Model
confidentiality32_ast = assertParseModel confidentiality32

confidentiality33 :: Text
confidentiality33 = $(embedStringFile "data/confidentiality33.vp")
confidentiality33_ast :: Model
confidentiality33_ast = assertParseModel confidentiality33

shamir1 :: Text
shamir1 = $(embedStringFile "data/shamir1.vp")
shamir1_ast :: Model
shamir1_ast = assertParseModel shamir1


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
freshness1ast :: Model
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
equivalence1_ast :: Model
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
equivalence2_ast :: Model
equivalence2_ast = assertParseModel equivalence2

equivalence3 :: Text
equivalence3 = $(embedStringFile "data/equivalence3.vp")
equivalence3_ast :: Model
equivalence3_ast = assertParseModel equivalence3

equivalence4 :: Text
equivalence4 = $(embedStringFile "data/equivalence4.vp")
equivalence4_ast :: Model
equivalence4_ast = assertParseModel equivalence4

equivalence5 :: Text
equivalence5 = $(embedStringFile "data/equivalence5.vp")
equivalence5_ast :: Model
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
bad_undefinedconstant_in_cfquery_ast :: Model
bad_undefinedconstant_in_cfquery_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "x",Private)]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "y"}}, queryOptions = Nothing}]]}

bad_early_constant :: Text
bad_early_constant = $(embedStringFile "data/bad_early_constant.vp")
bad_early_constant_ast :: Model
bad_early_constant_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = []}),ModelPrincipal (Principal {principalName = "B", principalKnows = []}),ModelMessage (Message {messageSender = "A", messageReceiver = "B", messageConstants = [(Constant {constantName = "yo"},False)]}),ModelPrincipal (Principal {principalName = "A", principalKnows = [(mkc "yo",Private)]})]}

model_concat :: Text
model_concat = $(embedStringFile "data/concat.vp")
model_concat_ast :: Model
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
              }), ModelQueries []]}

bad_knows_freshness :: Text
bad_knows_freshness = $(embedStringFile "data/bad_knows_freshness.vp")
bad_knows_freshness_ast :: Model
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
dup2model = Model Passive [mp "Alice" [privx, (mkc "x", Public)]]
dup3model = Model Passive [mp "Alice" [privx], mp "Bob" [privx]]
dup4model = Model Passive [mp "Alice" [privx], mp "Bob" [(mkc "x", Public)]]
mp :: PrincipalName -> [(NonEmpty Constant, Knowledge)] -> ModelPart
mp name knows = ModelPrincipal (Principal name knows)
privx :: (NonEmpty Constant, Knowledge)
privx = (mkc "x", Private)

------------------------------------------------------------------------------

challengeResponse :: Text
challengeResponse = $(embedStringFile "foreign_models/verifpal/test/challengeresponse.vp")

challengeResponseModel :: Model
challengeResponseModel = assertParseModel challengeResponse

foreignRingSign :: Text
foreignRingSign = $(embedStringFile "foreign_models/verifpal/test/ringsign.vp")

foreignRingSignModel :: Model
foreignRingSignModel = assertParseModel foreignRingSign

foreign_verifpal_test_ql :: Text
foreign_verifpal_test_ql = $(embedStringFile "foreign_models/verifpal/test/ql.vp")
foreign_verifpal_test_ql_ast :: Model
foreign_verifpal_test_ql_ast = assertParseModel foreign_verifpal_test_ql

foreign_verifpal_test_pw_hash :: Text
foreign_verifpal_test_pw_hash = $(embedStringFile "foreign_models/verifpal/test/pw_hash.vp")
foreign_verifpal_test_pw_hash_ast :: Model
foreign_verifpal_test_pw_hash_ast = assertParseModel foreign_verifpal_test_pw_hash

foreign_verifpal_test_pw_hash2 :: Text
foreign_verifpal_test_pw_hash2 = $(embedStringFile "foreign_models/verifpal/test/pw_hash2.vp")
foreign_verifpal_test_pw_hash2_ast :: Model
foreign_verifpal_test_pw_hash2_ast = assertParseModel foreign_verifpal_test_pw_hash2

-- principal A[generates a; c = b ]
-- this should give an error that "b" is unbound
bad_assignment_to_undefined_ast :: Model
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
