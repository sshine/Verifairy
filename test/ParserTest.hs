{-# LANGUAGE TemplateHaskell #-}

module ParserTest where

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
import VerifPal.Parser (parsePrincipal, parseModelPart, parseModel)

spec_parsePrincipal :: Spec
spec_parsePrincipal = do
  describe "parsePrincipal" $ do
    it "parses data/alice1.vp" $
      parsePrincipal alice1 `shouldParse` alice1ast

    it "parses data/bob1.vp" $
      parsePrincipal bob1 `shouldParse` bob1ast

    it "parses data/equations1.vp" $
      parsePrincipal equations1 `shouldParse` equations1ast

  describe "parseModelPart" $ do
    it "parses data/alice1.vp" $
      parseModelPart alice1 `shouldParse` ModelPrincipal alice1ast

    it "parses data/message1.vp" $
      parseModelPart message1 `shouldParse` ModelMessage message1ast

    it "parses data/phase1.vp" $
      parseModelPart phase1 `shouldParse` ModelPhase phase1ast

  describe "parseModel" $ do
    it "parses data/alice1model.vp" $
      parseModel alice1model `shouldParse` alice1modelast

    it "parses data/bob1model.vp" $
      parseModel bob1model `shouldParse` bob1modelast

    it "parses data/simple1.vp" $
      parseModel simple1 `shouldParse` simple1ast

    it "parses data/simple2.vp" $
      parseModel simple2 `shouldParse` simple2ast

alice1 :: Text
alice1 = $(embedStringFile "data/alice1.vp")

alice1ast :: Principal
alice1ast = Principal{..}
  where
    principalName = "Alice"
    principalKnows = Map.fromList
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
    principalKnows = Map.fromList
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
  , principalKnows = Map.fromList
      [ (Constant {constantName = "gx"},Assignment (G (EConstant (Constant {constantName = "x"}))))
      , (Constant {constantName = "gxy"},Assignment ((:^:) (Constant {constantName = "gx"}) (EConstant (Constant {constantName = "y"}))))
      , (Constant {constantName = "gy"},Assignment (G (EConstant (Constant {constantName = "y"}))))
      , (Constant {constantName = "gyx"},Assignment ((:^:) (Constant {constantName = "gy"}) (EConstant (Constant {constantName = "x"}))))
      , (Constant {constantName = "x"},Generates)
      , (Constant {constantName = "y"},Generates)
      ]
  }

alice1model :: Text
alice1model = $(embedStringFile "data/alice1model.vp")

alice1modelast :: Model
alice1modelast = Model
  { modelAttacker = Active
  , modelParts = [ ModelPrincipal (Principal { principalName = "Alice"
                                             , principalKnows = Map.fromList [(Constant {constantName = "a"},Generates)
                                                                         ,(Constant {constantName = "c0"},Public)
                                                                         ,(Constant {constantName = "c1"},Public)
                                                                         ,(Constant {constantName = "m1"},Private)
                                                                         ]
                                             }
                                  )
                 ]
  }

bob1model :: Text
bob1model = $(embedStringFile "data/bob1model.vp")

bob1modelast :: Model
bob1modelast = Model {modelAttacker = Passive, modelParts = [ModelPrincipal (Principal {principalName = "Bob", principalKnows = Map.fromList [(Constant {constantName = "b"},Generates),(Constant {constantName = "c0"},Public),(Constant {constantName = "c1"},Public),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "m2"},Private)]})]}

simple1 :: Text
simple1 = $(embedStringFile "data/simple1.vp")

simple1ast :: Model
simple1ast = Model
  { modelAttacker = Active
  , modelParts = [ ModelPrincipal (Principal { principalName = "Alice"
                                             , principalKnows = Map.fromList [(Constant {constantName = "a"},Generates)
                                             , (Constant {constantName = "ga"}
                                             , Assignment (G (EConstant (Constant {constantName = "a"}))))]})
                 , ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [Constant {constantName = "ga"}]})
                 , ModelPrincipal (Principal {principalName = "Bob", principalKnows = Map.fromList [(Constant {constantName = "b"},Generates),(Constant {constantName = "e1"},Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark)),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "m1"},Private),(Constant {constantName = "ss_a"},Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"}))))]})
                 , ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [Constant {constantName = "gb"},Constant {constantName = "e1"}]})
                 , ModelPrincipal (Principal {principalName = "Alice", principalKnows = Map.fromList [(Constant {constantName = "e1_dec"},Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark)),(Constant {constantName = "ss_b"},Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"}))))]})]
  }

simple2 :: Text
simple2 = $(embedStringFile "data/simple2.vp")

simple2ast :: Model
simple2ast = Model {modelAttacker = Active, modelParts = [ModelPrincipal (Principal {principalName = "Alice", principalKnows = Map.fromList [(Constant {constantName = "a"},Generates),(Constant {constantName = "ga"},Assignment (G (EConstant (Constant {constantName = "a"}))))]}),ModelMessage (Message {messageSender = "Alice", messageReceiver = "Bob", messageConstants = [Constant {constantName = "ga"}]}),ModelPrincipal (Principal {principalName = "Bob", principalKnows = Map.fromList [(Constant {constantName = "b"},Generates),(Constant {constantName = "e1"},Assignment (EPrimitive (AEAD_ENC (EConstant (Constant {constantName = "ss_a"})) (EConstant (Constant {constantName = "m1"})) (EConstant (Constant {constantName = "gb"}))) HasntQuestionMark)),(Constant {constantName = "gb"},Assignment (G (EConstant (Constant {constantName = "b"})))),(Constant {constantName = "m1"},Private),(Constant {constantName = "ss_a"},Assignment ((:^:) (Constant {constantName = "ga"}) (EConstant (Constant {constantName = "b"}))))]}),ModelMessage (Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [Constant {constantName = "gb"},Constant {constantName = "e1"}]}),ModelPrincipal (Principal {principalName = "Alice", principalKnows = Map.fromList [(Constant {constantName = "e1_dec"},Assignment (EPrimitive (AEAD_DEC (EConstant (Constant {constantName = "ss_b"})) (EConstant (Constant {constantName = "e1"})) (EConstant (Constant {constantName = "gb"}))) HasQuestionMark)),(Constant {constantName = "ss_b"},Assignment ((:^:) (Constant {constantName = "gb"}) (EConstant (Constant {constantName = "a"}))))]}),ModelQueries [Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "e1"}}, queryOptions = Nothing},Query {queryKind = ConfidentialityQuery {confidentialityConstant = Constant {constantName = "m1"}}, queryOptions = Nothing},Query {queryKind = AuthenticationQuery {authenticationMessage = Message {messageSender = "Bob", messageReceiver = "Alice", messageConstants = [Constant {constantName = "e1"}]}}, queryOptions = Nothing},Query {queryKind = EquivalenceQuery {equivalenceConstants = [Constant {constantName = "ss_a"},Constant {constantName = "ss_b"}]}, queryOptions = Nothing}]]}

message1 :: Text
message1 = $(embedStringFile "data/message1.vp")

message1ast :: Message
message1ast = Message "Alice" "Bob" [Constant "x"]

phase1 :: Text
phase1 = $(embedStringFile "data/phase1.vp")

phase1ast :: Phase
phase1ast = Phase 42

