
-- https://source.symbolic.software/verifpal/verifpal/-/blob/master/cmd/vplogic/libpeg.go

module VerifPal.Parser where

import Control.Monad (void)
import Data.Char (isLetter, isSpace, isNumber)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Megaparsec
import Text.Megaparsec.Char (eol)
import Text.Megaparsec.Char.Lexer (decimal)
import Data.Void (Void)

import VerifPal.Types

type Parser = Parsec Void Text

parse' :: Parser a -> Text -> Either (ParseErrorBundle Text Void) a
parse' p = parse p ""

parsePrincipal :: Text -> Either (ParseErrorBundle Text Void) Principal
parsePrincipal = parse' principal

parseModel :: Text -> Either (ParseErrorBundle Text Void) Model
parseModel = parse' model

model :: Parser Model
model = do
  space
  modelAttacker <- attacker
  modelParts <- many modelPart
  modelQueries <- queries
  pure Model{..}

attacker :: Parser Attacker
attacker = do
  symbol0 "attacker"
  brackets $ choice [ active, passive ]
  where
    active = symbol "active" >> pure Active
    passive = symbol "passive" >> pure Passive

modelPart :: Parser ModelPart
modelPart = choice
  [ ModelPrincipal <$> principal
  , ModelMessage <$> message
  , ModelPhase <$> phase
  ]

principal :: Parser Principal
principal = do
  symbol1 "principal"
  principalName <- name
  principalKnows <- brackets statements
  pure Principal{..}

-- Bob -> Alice: gb, e1
message :: Parser Message
message = do
  messageSender <- name
  symbol0 "->"
  messageReceiver <- name
  symbol0 ":"
  messageConstants <- constant `sepBy1` comma
  pure Message{..}

phase :: Parser Phase
phase = do
  symbol0 "phase"
  phaseNumber <- brackets decimal
  pure Phase{..}

queries :: Parser [Query]
queries = do
  symbol0 "queries"
  brackets (many query)

query :: Parser Query
query = do
  queryKind <- choice
    [ confidentialityQuery
    , authenticationQuery
    , freshnessQuery
    , unlinkabilityQuery
    , equivalenceQuery
    ]
  queryOptions <- queryOption
  pure Query{..}
  where
    confidentialityQuery = do
      symbol0 "confidentiality?" 
      ConfidentialityQuery <$> constant

    -- FIXME: I'm using 'message' here, but the BNF doesn't actually allow the full flexibility of Message here.
    authenticationQuery = do
      symbol0 "authentication?"
      AuthenticationQuery <$> message

    freshnessQuery = do
      symbol0 "freshness?"
      FreshnessQuery <$> constant

    unlinkabilityQuery = do
      symbol0 "unlinkability?"
      UnlinkabilityQuery <$> (constant `sepBy1` comma)

    equivalenceQuery = do
      symbol0 "equivalence?"
      EquivalenceQuery <$> (constant `sepBy1` comma)

    queryOption :: Parser QueryOption
    queryOption = do
      symbol0 "precondition"
      QueryOption <$> brackets message

statements :: Parser (Map Constant Knowledge)
statements = Map.fromList . concat <$> many knowledge

knowledge :: Parser [(Constant, Knowledge)]
knowledge = do
  line <- choice [ knows, generates, leaks, assignment ]
  lexeme0 eol
  pure line
  where
    knows = do
      symbol1 "knows"
      visibility <- publicPrivatePassword
      cs <- constant `sepBy1` comma
      pure [ (c, visibility) | c <- cs ]

    generates :: Parser [(Constant, Knowledge)]
    generates = do
      symbol1 "generates"
      cs <- constant `sepBy1` comma
      pure [ (c, Generates) | c <- cs ]

    leaks :: Parser [(Constant, Knowledge)]
    leaks = do
      symbol1 "leaks"
      cs <- constant `sepBy1` comma
      pure [ (c, Leaks) | c <- cs ]

    assignment :: Parser [(Constant, Knowledge)]
    assignment = do
      c <- constant
      symbol0 "="
      e <- expr
      pure [(c, Assignment e)]

expr :: Parser Expr
expr = choice [ g, constHat ]
  where
    g, constHat :: Parser Expr
    g = do
      symbol0 "G^"
      G <$> expr

    constHat = do
      c <- constant
      maybeHat <- option Const $ do
        symbol0 "^"
        e <- expr
        pure (:^: e)
      pure (maybeHat c)

publicPrivatePassword :: Parser Knowledge
publicPrivatePassword = choice
  [ symbol1 "public" >> pure Public
  , symbol1 "private" >> pure Private
  , symbol1 "password" >> pure Password
  ]

name :: Parser Text
name = identifier "principal name"

constant :: Parser Constant
constant = lexeme0 $ Constant <$> identifier "constant"

identifier :: String -> Parser Text
identifier desc = lexeme0 $ do
  ident <- takeWhile1P (Just desc) isIdentifierChar
  if ident `elem` reservedKeywords
    then error ("keyword '" <> Text.unpack ident <> "' not allowed as " <> desc) -- FIXME: Use Megaparsec error handling
    else return ident

comma :: Parser ()
comma = symbol0 ","

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

symbol, symbol0, symbol1 :: Text -> Parser ()
symbol = lexeme . void . chunk
symbol0 = lexeme0 . void . chunk
symbol1 = lexeme1 . void . chunk

lexeme, lexeme0, lexeme1 :: Parser a -> Parser a
lexeme = (<* space)
lexeme0 = (<* space0)
lexeme1 = (<* space1)

space, space0, space1 :: Parser ()
space = void $ takeWhileP (Just "any whitespace") isSpace
space0 = void $ takeWhileP (Just "") isHorizontalSpace
space1 = void $ takeWhile1P (Just "whitespace 3") isHorizontalSpace

isHorizontalSpace :: Char -> Bool
isHorizontalSpace c = isSpace c && c /= '\r' && c /= '\n'

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isLetter c || isNumber c

reservedKeywords :: [Text]
reservedKeywords =
  [ "active"
  , "aead_dec"
  , "aead_enc"
  , "assert"
  , "attacker"
  , "authentication"
  , "concat"
  , "confidentiality"
  , "dec"
  , "enc"
  , "equivalence"
  , "freshness"
  , "generates"
  , "hash"
  , "hkdf"
  , "knows"
  , "leaks"
  , "mac"
  , "passive"
  , "password"
  , "phase"
  , "pke_dec"
  , "pke_enc"
  , "precondition"
  , "primitive"
  , "principal"
  , "private"
  , "public"
  , "pw_hash"
  , "ringsign"
  , "ringsignverif"
  , "shamir_join"
  , "shamir_split"
  , "sign"
  , "signverif"
  , "split"
  , "unlinkability"
  , "unnamed"
  ]
