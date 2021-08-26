
-- https://source.symbolic.software/verifpal/verifpal/-/blob/master/cmd/vplogic/libpeg.go

module VerifPal.Parser where

import Control.Monad (void)
import Data.Char (isLetter, isSpace, isNumber)
import Data.Functor (($>))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Megaparsec
import Text.Megaparsec.Char (eol, digitChar)
import Text.Megaparsec.Char.Lexer (decimal)
import Data.Void (Void)

import VerifPal.Types

type Parser = Parsec Void Text

parse' :: Parser a -> Text -> Either (ParseErrorBundle Text Void) a
parse' p = parse p ""

parsePrincipal :: Text -> Either (ParseErrorBundle Text Void) Principal
parsePrincipal = parse' principal

parseModelPart :: Text -> Either (ParseErrorBundle Text Void) ModelPart
parseModelPart = parse' modelPart

parseModel :: Text -> Either (ParseErrorBundle Text Void) Model
parseModel = parse' (space *> model)

model :: Parser Model
model = do
  modelAttacker <- attacker
  modelParts <- many modelPart
  pure Model{..}

attacker :: Parser Attacker
attacker = do
  symbol "attacker"
  brackets $ choice [ active, passive ]
  where
    active = symbol "active" >> pure Active
    passive = symbol "passive" >> pure Passive

modelPart :: Parser ModelPart
modelPart = choice
  [ ModelPrincipal <$> principal
  , ModelPhase <$> phase
  , ModelQueries <$> queries
  , ModelMessage <$> message
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
  symbol "->"
  messageReceiver <- name
  symbol ":"
  messageConstants <- constant `sepBy1` comma
  pure Message{..}

phase :: Parser Phase
phase = do
  symbol "phase"
  Phase . read <$> brackets (some digitChar)

queries :: Parser [Query]
queries = do
  symbol "queries"
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
  queryOptions <- option Nothing (Just <$> queryOption)
  pure Query{..}
  where
    confidentialityQuery = do
      symbol "confidentiality?" 
      ConfidentialityQuery <$> constant

    -- FIXME: I'm using 'message' here, but the BNF doesn't actually allow the full flexibility of Message here.
    authenticationQuery = do
      symbol "authentication?"
      AuthenticationQuery <$> message

    freshnessQuery = do
      symbol "freshness?"
      FreshnessQuery <$> constant

    unlinkabilityQuery = do
      symbol "unlinkability?"
      UnlinkabilityQuery <$> (constant `sepBy1` comma)

    equivalenceQuery = do
      symbol "equivalence?"
      EquivalenceQuery <$> (constant `sepBy1` comma)

    queryOption :: Parser QueryOption
    queryOption = do
      symbol "precondition"
      QueryOption <$> brackets message

statements :: Parser [(Constant, Knowledge)]
statements = concat <$> many knowledge

knowledge :: Parser [(Constant, Knowledge)]
knowledge = choice [ knows, generates, leaks, assignment ]
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
      symbol "="
      e <- expr
      pure [(c, Assignment e)]

expr :: Parser Expr
expr = choice [ g, primitive, constHat ]
  where
    g, primitive, constHat :: Parser Expr
    g = do
      symbol "G^"
      G <$> expr

    primitive = choice
      [ prim2 "ASSERT" ASSERT
      , primN "CONCAT" CONCAT
      , prim1 "SPLIT" SPLIT
      , primN "HASH" HASH
      , prim2 "MAC" MAC
      , prim3 "HKDF" HKDF
      , primN "PW_HASH" PW_HASH
      , prim2 "ENC" ENC
      , prim2 "DEC" DEC
      , prim3 "AEAD_ENC" AEAD_ENC
      , prim3 "AEAD_DEC" AEAD_DEC
      , prim2 "PKE_ENC" PKE_ENC
      , prim2 "PKE_DEC" PKE_DEC
      , prim2 "SIGN" SIGN
      , prim3 "SIGNVERIF" SIGNVERIF
      , prim4 "RINGSIGN" RINGSIGN
      , prim5 "RIGNSIGNVERIF" RINGSIGNVERIF
      , prim2 "BLIND" BLIND
      , prim3 "UNBLIND" UNBLIND
      , prim1 "SHAMIR_SPLIT" SHAMIR_SPLIT
      , prim3 "SHAMIR_JOIN" SHAMIR_JOIN
      ]

    prim1 :: Text -> (Expr -> Primitive) -> Parser Expr
    prim1 primName primOp = do
      prim <- parens (primOp <$> expr)
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    prim2 :: Text -> (Expr -> Expr -> Primitive) -> Parser Expr
    prim2 primName primOp = do
      symbol primName
      prim <- parens (primOp <$> (expr <* comma) <*> expr)
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    prim3 :: Text -> (Expr -> Expr -> Expr -> Primitive) -> Parser Expr
    prim3 primName primOp = do
      symbol primName
      prim <- parens (primOp <$> (expr <* comma) <*> (expr <* comma) <*> expr)
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    prim4 :: Text -> (Expr -> Expr -> Expr -> Expr -> Primitive) -> Parser Expr
    prim4 primName primOp = do
      symbol primName
      prim <- parens (primOp <$> (expr <* comma) <*> (expr <* comma) <*> (expr <* comma) <*> expr)
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    prim5 :: Text -> (Expr -> Expr -> Expr -> Expr -> Expr -> Primitive) -> Parser Expr
    prim5 primName primOp = do
      symbol primName
      prim <- parens (primOp <$> (expr <* comma) <*> (expr <* comma) <*> (expr <* comma) <*> (expr <* comma) <*> expr)
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    primN :: Text -> ([Expr] -> Primitive) -> Parser Expr
    primN primName primOp = do
      symbol primName
      prim <- parens (primOp <$> (expr `sepBy` comma))
      question <- option HasntQuestionMark (symbol "?" $> HasQuestionMark)
      pure (EPrimitive prim question)

    constHat = do
      c <- constant
      maybeHat <- option EConstant $ do
        symbol "^"
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
constant = Constant <$> identifier "constant"

-- FIXME: "queries[...]" fails because it's being parsed as a Message sender
identifier :: String -> Parser Text
identifier desc = lexeme (try (ident >>= check))
  where
    ident = takeWhile1P (Just desc) isIdentifierChar
    check s
      | s `notElem` reservedKeywords = pure s
      | otherwise = fail ("Cannot use '" <> Text.unpack s <> "' as identifier")

comma :: Parser ()
comma = symbol ","

brackets, parens :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")
parens = between (symbol "(") (symbol ")")

symbol, symbol1 :: Text -> Parser ()
symbol = lexeme . void . chunk
symbol1 = lexeme1 . void . chunk

lexeme, lexeme1 :: Parser a -> Parser a
lexeme = (<* space)
lexeme1 = (<* space1)

space, space1 :: Parser ()
space = void $ takeWhileP (Just "any whitespace") isSpace
space1 = void $ takeWhile1P (Just "at least one whitespace") isSpace

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isLetter c || isNumber c || c == '_'

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
