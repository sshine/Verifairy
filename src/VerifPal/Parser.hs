
module VerifPal.Parser where

import Control.Monad (void)
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Megaparsec
import Text.Megaparsec.Char (space, digitChar, char, char')
import Data.Void (Void)

import VerifPal.Types

type Parser = Parsec Void Text

parse' :: Parser a -> Text -> Either (ParseErrorBundle Text Void) a
parse' p = parse p ""

parsePrincipal :: Text -> Either (ParseErrorBundle Text Void) Principal
parsePrincipal = parse' principal

principal :: Parser Principal
principal = do
  symbol "principal"
  pure emptyPrincipal

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

symbol :: Text -> Parser ()
symbol = lexeme . void . chunk

lexeme :: Parser a -> Parser a
lexeme = (<* space)
