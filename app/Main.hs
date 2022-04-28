{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE  MultiParamTypeClasses #-}
module Main where

import           Data.Foldable (for_)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import           Options.Applicative
import           System.Environment (getArgs)
import           System.Exit (exitFailure)
import           System.FilePath.Posix ((</>))
import           System.IO (stderr)
import GitHash
import Data.Void

import Error.Diagnose (printDiagnostic, addFile)
import Error.Diagnose.Compat.Megaparsec ( HasHints(hints), errorDiagnosticFromBundle )
--import Error.Diagnose.Compat.Megaparsec

import VerifPal.Parser (parseModel)

type OutputFile = (FilePath, Text)
type Backend = FilePath -> Text -> Either Text [OutputFile]

backends :: [(Text, Backend)]
backends = [ ]

data Args = Args
  { srcFile :: FilePath -- ^ The .vp model file
  , outDir  :: FilePath -- ^ TODO
  , backend :: Text     -- ^ TODO
  } deriving (Show)

main :: IO ()
main = runArgsParser >>= argsHandler
-- see: https://github.com/Mesabloo/diagnose/blob/master/test/rendering/Spec.hs
instance HasHints Void Text where
  -- hints :: Void -> [Text]
  hints _ = ["TODOwhatisthis"]

argsHandler :: Args -> IO ()
argsHandler Args { backend = backend
                 , srcFile = srcFile
                 , outDir = outDir
                 } = do
  srcText <- Text.readFile srcFile
  case parseModel srcText of
    Left bundle ->
      let
        short       = Nothing :: Maybe Text
        explanation = "Parse error on input"
        extra_hints = Nothing :: Maybe [Text] -- in addition to the HasHints lookup?
        diag  = errorDiagnosticFromBundle short explanation extra_hints (bundle)
        diag' = addFile diag srcFile (Text.unpack srcText)
      in printDiagnostic stderr True True 4 diag'
    Right model -> do
      Text.hPutStrLn stderr ("parsing file " <> Text.pack "x" <> "...")
      print "yo"
      --Text.writeFile outFilePath outText

runArgsParser :: IO Args
runArgsParser = customExecParser (prefs showHelpOnError) argsParserInfo

gitBuildInfo :: String
gitBuildInfo =
  concat [ giBranch gi, "@", giHash gi, dirty
         , " (", giCommitDate gi, ")"]
  where
    dirty | giDirty gi = "~dirty"
          | otherwise   = ""
    gi = $$tGitInfoCwd

argsParserInfo :: ParserInfo Args
argsParserInfo =
  info (helper <*> argsParser) . mconcat $
    [ fullDesc
    , header ("verifairy " <> gitBuildInfo)
    , progDesc "Deals with VerifPal models"
    ]

argsParser :: Parser Args
argsParser = Args <$> srcFileParser <*> outDirParser <*> backendParser
  where
    srcFileParser = strArgument . mconcat $
      [ metavar "<FILE.vp>"
      ]

    outDirParser = strOption . mconcat $
      [ long "output"
      , short 'o'
      , metavar "DIRECTORY"
      , help "Output directory for compiled contract"
      , value "."
      , showDefault
      ]

    backendParser = strOption . mconcat $
      [ long "backend"
      , short 'b'
      , metavar "BACKEND"
      , help "The code generator to use"
      , value "evm"
      , showDefault
      ]

commas :: [Text] -> Text
commas = Text.intercalate ", "

meh :: Text -> IO ()
meh message = do
  Text.hPutStrLn stderr message
  exitFailure
