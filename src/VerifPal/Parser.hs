
module VerifPal.Parser where

import Control.Monad (void)
import Data.Char (isLetter, isSpace)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Megaparsec
import Text.Megaparsec.Char (eol)
import Data.Void (Void)

import VerifPal.Types

type Parser = Parsec Void Text

parse' :: Parser a -> Text -> Either (ParseErrorBundle Text Void) a
parse' p = parse p ""

parsePrincipal :: Text -> Either (ParseErrorBundle Text Void) Principal
parsePrincipal = parse' principal

principal :: Parser Principal
principal = do
  symbol1 "principal"
  principalName <- name
  principalKnows <- brackets statements
  pure Principal{..}

statements :: Parser (Map Constant Knowledge)
statements = Map.fromList . concat <$> many knowledge

knowledge :: Parser [(Constant, Knowledge)]
knowledge = choice [ knows, generates ] <* eol
  where
    knows = do
      symbol1 "knows"
      visibility <- publicPrivate
      cs <- constant `sepBy1` comma
      pure [ (c, visibility) | c <- cs ]

    generates :: Parser [(Constant, Knowledge)]
    generates = do
      symbol1 "generates"
      cs <- constant `sepBy1` comma
      pure [ (c, Generates) | c <- cs ]

publicPrivate :: Parser Knowledge
publicPrivate = choice
  [ symbol1 "public" >> pure Public
  , symbol1 "private" >> pure Private
  ]

name :: Parser Text
name = lexeme0 $ takeWhile1P (Just "principal name") isLetter

constant :: Parser Constant
constant = Constant <$> takeWhile1P Nothing isLetter

comma :: Parser ()
comma = symbol1 ", "

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

symbol, symbol1 :: Text -> Parser ()
symbol = lexeme . void . chunk
symbol1 = lexeme1 . void . chunk

lexeme, lexeme0, lexeme1 :: Parser a -> Parser a
lexeme = (<* space)
lexeme0 = (<* space0)
lexeme1 = (<* space1)

space, space0, space1 :: Parser ()
space = void $ takeWhileP (Just "whitespace") isSpace
space0 = void $ takeWhileP (Just "whitespace") isHorizontalSpace
space1 = void $ takeWhile1P (Just "whitespace") isHorizontalSpace

isHorizontalSpace :: Char -> Bool
isHorizontalSpace c = isSpace c && c /= '\r' && c /= '\n'
