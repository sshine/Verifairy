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
import Test.Hspec.Megaparsec
import Test.Tasty.Hspec
--import Text.Megaparsec (parse, ParseErrorBundle)
--import Text.RawString.QQ
--import Text.Read (readEither)

import VerifPal.Types
import VerifPal.Parser (parsePrincipal)

--shouldParseAs :: Text -> Expr -> Spec
--shouldParseAs s e =
--  it (Text.unpack s) $ parseExpr s `shouldParse` e

spec_FuncDef :: Spec
spec_FuncDef =
  describe "parsePrincipal" $ do
    it "parses data/alice1.vp" $
      parsePrincipal alice1 `shouldParse` alice1ast

    it "parses data/bob1.vp" $
      parsePrincipal bob1 `shouldParse` bob1ast

  where
    alice1 :: Text
    alice1 = $(embedStringFile "data/alice1.vp")

    alice1ast :: Principal
    alice1ast = Principal $ Map.fromList
      [ (Constant "c0", Public)
      , (Constant "c1", Public)
      , (Constant "m1", Private)
      , (Constant "a", Generates)
      ]

    bob1 :: Text
    bob1 = $(embedStringFile "data/bob1.vp")

    bob1ast :: Principal
    bob1ast = Principal $ Map.fromList
      [ (Constant "c0", Public)
      , (Constant "c1", Public)
      , (Constant "m2", Private)
      , (Constant "a", Generates)
      , (Constant "gb", Assignment (G (Const "b")))
      ]
