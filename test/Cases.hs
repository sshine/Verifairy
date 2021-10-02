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

import VerifPal.Types

alice1 :: Text
alice1 = $(embedStringFile "data/alice1.vp")

alice1ast :: Principal
alice1ast = Principal{..}
  where
    principalName = "Alice"
    principalKnows =
      [ (Constant "c0", Public)
      , (Constant "c1", Public)
      , (Constant "m1", Private)
      , (Constant "a", Generates)
      ]

bob1 :: Text
bob1 = $(embedStringFile "data/bob1.vp")

bob1ast :: Principal
bob1ast = Principal{..}
  where
    principalName = "Bob"
    principalKnows =
      [ (Constant "c0", Public)
      , (Constant "c1", Public)
      , (Constant "m2", Private)
      , (Constant "b", Generates)
      , (Constant "gb", Assignment (G (mkConst "b")))
      ]

equations1 :: Text
equations1 = $(embedStringFile "data/equations1.vp")

equations1ast :: Principal
equations1ast = Principal
  { principalName = "Server"
  , principalKnows =
      [ (Constant {constantName = "x"},Generates)
      , (Constant {constantName = "y"},Generates)
      , (Constant {constantName = "gx"},Assignment (G (EConstant (Constant {constantName = "x"}))))
      , (Constant {constantName = "gy"},Assignment (G (EConstant (Constant {constantName = "y"}))))
      , (Constant {constantName = "gxy"},Assignment ((:^:) (Constant {constantName = "gx"}) (EConstant (Constant {constantName = "y"}))))
      , (Constant {constantName = "gyx"},Assignment ((:^:) (Constant {constantName = "gy"}) (EConstant (Constant {constantName = "x"}))))
      ]
  }

alice1model :: Text
alice1model = $(embedStringFile "data/alice1model.vp")

alice1modelast :: Model
alice1modelast = Model
  { modelAttacker = Active
  , modelParts = [ ModelPrincipal (Principal { principalName = "Alice", principalKnows = aliceKnows })]
  }
  where
    aliceKnows =
      [ (Constant {constantName = "c0"},Public)
      , (Constant {constantName = "c1"},Public)
      , (Constant {constantName = "m1"},Private)
      , (Constant {constantName = "a"},Generates)
      ]

bob1model :: Text
bob1model = $(embedStringFile "data/bob1model.vp")

bob1modelast :: Model
bob1modelast = Model
  { modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "Bob", principalKnows = bobKnows })] }
  where
    bobKnows =
      [ (Constant {constantName = "c0"},Public)
      , (Constant {constantName = "c1"},Public)
      , (Constant {constantName = "m2"},Private)
      , (Constant {constantName = "b"},Generates)
      , (Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"}))))
      ]

simple1 :: Text
simple1 = $(embedStringFile "data/simple1.vp")

simple1ast :: Model
simple1ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "a"},Generates),(Constant {constantName = "ga"},Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ga"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(Constant {constantName = "m1"},Private),(Constant {constantName = "b"},Generates),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "ss_a"},Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "e1"},Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "gb"},False),(Constant {constantName = "e1"},False)]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "ss_b"},Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"})))),(Constant {constantName = "e1_dec"},Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark))]})]}

simple1_complete_active :: Text
simple1_complete_active = $(embedStringFile "data/simple1_complete_active.vp")

simple1_complete_active_ast :: Model
simple1_complete_active_ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "a"},Generates),(Constant {constantName = "ga"},Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ga"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(Constant {constantName = "m1"},Private),(Constant {constantName = "b"},Generates),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "ss_a"},Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "e1"},Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "gb"},False),(Constant {constantName = "e1"},False)]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "ss_b"},Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"})))),(Constant {constantName = "e1_dec"},Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark))]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "e1"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "m1"}}, queryOptions = Nothing},Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "e1"},False)]}}, queryOptions = Nothing},Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "ss_a"},Constant {constantName = "ss_b"}]}, queryOptions = Nothing}]]}

simple1_complete_passive :: Text
simple1_complete_passive = $(embedStringFile "data/simple1_complete_passive.vp")

simple1_complete_passive_ast :: Model
simple1_complete_passive_ast = Model Passive []

simple2 :: Text
simple2 = $(embedStringFile "data/simple2.vp")

simple2ast :: Model
simple2ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "a"},Generates),(Constant {constantName = "ga"},Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ga"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(Constant {constantName = "m1"},Private),(Constant {constantName = "b"},Generates),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "ss_a"},Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "e1"},Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "gb"},False),(Constant {constantName = "e1"},False)]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "ss_b"},Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"})))),(Constant {constantName = "e1_dec"},Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark))]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "e1"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "m1"}}, queryOptions = Nothing},Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [(Constant {constantName = "e1"},False)]}}, queryOptions = Nothing},Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "ss_a"},Constant {constantName = "ss_b"}]}, queryOptions = Nothing}]]}

message1 :: Text
message1 = $(embedStringFile "data/message1.vp")

message1ast :: Message
message1ast = Message "Alice" "Bob" [(Constant "x", False)]

phase1 :: Text
phase1 = $(embedStringFile "data/phase1.vp")

phase1ast :: Phase
phase1ast = Phase 42

freshness2 :: Text
freshness2 = $(embedStringFile "data/freshness2.vp")

freshness2ast :: Model
freshness2ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = [(Constant {constantName = "a"},Private),(Constant {constantName = "b"},Generates),(Constant {constantName = "ha"},Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)),(Constant {constantName = "hb"},Assignment (EPrimitive (HASH [EConstant (Constant {constantName = "b"})]) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [(Constant {constantName = "ha"},False),(Constant {constantName = "hb"},False)]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = [(Constant {constantName = "a"},Private),(Constant {constantName = "_"},Assignment (EPrimitive (ASSERT (EConstant (Constant {constantName = "ha"})) (EPrimitive (HASH [EConstant (Constant {constantName = "a"})]) HasntQuestionMark)) HasntQuestionMark))]}),ModelQueries [Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "ha"}}, queryOptions = Nothing},Query {queryKind = FreshnessQuery {freshnessConstant = Constant {constantName = "hb"}}, queryOptions = Nothing}]]}

abknows :: Text
abknows = $(embedStringFile "data/abknows.vp")

abknowsast :: Model
abknowsast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(Constant {constantName = "x"},Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(Constant {constantName = "x"},Private)]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "x"}}, queryOptions = Nothing}]]}

bad_publicprivate :: Text
bad_publicprivate = $(embedStringFile "data/bad_publicprivate.vp")

bad_publicprivate_ast :: Model
bad_publicprivate_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(Constant {constantName = "x"},Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(Constant {constantName = "x"},Public)]})]}

bad_passwordprivate :: Text
bad_passwordprivate = $(embedStringFile "data/bad_passwordprivate.vp")

bad_passwordprivate_ast :: Model
bad_passwordprivate_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(Constant {constantName = "x"},Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(Constant {constantName = "x"},Password)]})]}

bad_generatesknows :: Text
bad_generatesknows = $(embedStringFile "data/bad_generatesknows.vp")

bad_generatesknows_ast :: Model
bad_generatesknows_ast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "A", principalKnows = [(Constant {constantName = "x"},Private)]}),ModelPrincipal (Principal {principalName = "B", principalKnows = [(Constant {constantName = "x"},Generates)]})]}

-- Negative cases

dup1model, dup2model, dup3model, dup4model :: Model
dup1model = Model Passive [mp "Alice" [privx, privx]]
dup2model = Model Passive [mp "Alice" [privx, pubx]]
dup3model = Model Passive [mp "Alice" [privx], mp "Bob" [privx]]
dup4model = Model Passive [mp "Alice" [privx], mp "Bob" [pubx]]

mp name knows = ModelPrincipal (Principal name knows)
privx = (Constant "x", Private)
pubx = (Constant "x", Public)

------------------------------------------------------------------------------

challengeResponse :: Text
challengeResponse = $(embedStringFile "foreign_models/verifpal/test/challengeresponse.vp")

challengeResponseModel :: Model
challengeResponseModel = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Server", principalKnows = [(Constant {constantName = "s"},Private),(Constant {constantName = "gs"},Assignment (G (EConstant (Constant {constantName = "s"}))))]}),ModelPrincipal (Principal {principalName = "Client", principalKnows = [(Constant {constantName = "c"},Private),(Constant {constantName = "gc"},Assignment (G (EConstant (Constant {constantName = "c"})))),(Constant {constantName = "nonce"},Generates)]}),ModelMessage (Message {messageSender = "Client", messageReceiver = "Server", messageConstants = [(Constant {constantName = "nonce"},False)]}),ModelPrincipal (Principal {principalName = "Server", principalKnows = [(Constant {constantName = "proof"},Assignment (EPrimitive (SIGN (EConstant (Constant {constantName = "s"})) (EConstant (Constant {constantName = "nonce"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Server", messageReceiver = "Client", messageConstants = [(Constant {constantName = "gs"},True),(Constant {constantName = "proof"},False)]}),ModelPrincipal (Principal {principalName = "Client", principalKnows = [(Constant {constantName = "valid"},Assignment (EPrimitive (SIGNVERIF (EConstant (Constant {constantName = "gs"})) (EConstant (Constant {constantName = "nonce"})) (EConstant (Constant {constantName = "proof"}))) HasQuestionMark)),(Constant {constantName = "attestation"},Generates),(Constant {constantName = "signed"},Assignment (EPrimitive (SIGN (EConstant (Constant {constantName = "c"})) (EConstant (Constant {constantName = "attestation"}))) HasntQuestionMark))]}),ModelMessage (Message {messageSender = "Client", messageReceiver = "Server", messageConstants = [(Constant {constantName = "gc"},False),(Constant {constantName = "attestation"},False),(Constant {constantName = "signed"},False)]}),ModelPrincipal (Principal {principalName = "Server", principalKnows = [(Constant {constantName = "storage"},Assignment (EPrimitive (SIGNVERIF (EConstant (Constant {constantName = "gc"})) (EConstant (Constant {constantName = "attestation"})) (EConstant (Constant {constantName = "signed"}))) HasQuestionMark))]}),ModelQueries [Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Server", messageReceiver = "Client", messageConstants = [(Constant {constantName = "proof"},False)]}}, queryOptions = Nothing},Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Client", messageReceiver = "Server", messageConstants = [(Constant {constantName = "signed"},False)]}}, queryOptions = Nothing}]]}
