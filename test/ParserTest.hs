{-# LANGUAGE TemplateHaskell #-}

module ParserTest where

import Control.Monad
import Data.Char (chr, isHexDigit)
import Data.FileEmbed
import Data.Foldable (for_)
import qualified Data.Text as Text
import Data.Text (Text)
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
      parsePrincipal alice1 `shouldParse` emptyPrincipal

    it "parses data/bob1.vp" $
      parsePrincipal bob1 `shouldParse` emptyPrincipal

  where
    alice1, bob1 :: Text
    alice1 = $(embedStringFile "data/alice1.vp")
    bob1 = $(embedStringFile "data/bob1.vp")

