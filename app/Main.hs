module Main where

import Control.Monad (unless)
import Data.Foldable (for_, traverse_)
import Data.Function ((&))
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (addFile, printDiagnostic)
import Error.Diagnose.Compat.Megaparsec (errorDiagnosticFromBundle)
import Options.Applicative
import Prettyprinter.Render.Terminal (putDoc)
import System.Exit (exitFailure)
import System.IO (stderr)
import VerifPal.Check (ModelState (..), process, CanonExpr, canonicalizeExpr, simplifyExpr)
import VerifPal.Parser (parseModel)
import VerifPal.Pretty (myAnnotate, prettifyModelState, prettifyCanonExpr)
import VerifPal.Version (gitBuildInfo)
import VerifPal.Types (Knowledge(..), Constant(..), Expr(..))
import Data.Map(lookup)

data Args = Args
  { srcFile :: FilePath,
    simplify :: String,
    verbose :: Bool
  }
  deriving (Show)

main :: IO ()
main = runArgsParser >>= argsHandler

argsHandler :: Args -> IO ()
argsHandler Args {srcFile = srcFile, simplify=simplify, verbose = verbose} = do
  srcText <- Text.readFile srcFile
  case parseModel srcText of
    Left bundle ->
      let short = Nothing :: Maybe Text
          explanation = "Parse error on input"
          extra_hints = Nothing :: Maybe [Text] -- in addition to the HasHints lookup?
          diag = errorDiagnosticFromBundle short explanation extra_hints bundle
          fake_filename = "" -- TODO Parser.hs feeds in "" as the filename to "parse"
          diag' = addFile diag fake_filename (Text.unpack srcText)
       in printDiagnostic stderr True True 4 diag'
    Right model -> do
      Text.hPutStrLn stderr ("Processing file " <> Text.pack srcFile <> "...")
      let ms = VerifPal.Check.process model
      --
      case simplify of
        "" -> pure ()
        simplified ->
          do putStrLn ""
             let target = EConstant (Constant {constantName = Text.pack simplified})
                 constmap = msConstants ms
                 c_expr = canonicalizeExpr constmap target
             putDoc (prettifyCanonExpr c_expr)
             putStrLn ""
             putStrLn "================ simplifies to ->"
             putDoc (prettifyCanonExpr (simplifyExpr c_expr))
             putStrLn ""
      --
      unless (not verbose) $
        do putStrLn ""
           putDoc (prettifyModelState ms)
           putStrLn ""
      -- TODO should make a Diagnostic here for each of these:
      traverse_ print (msErrors ms)
      msQueryResults ms & map myAnnotate & for_ $ \annotated -> do
        putDoc annotated
        putStrLn ""
      -- Bail out if we have errors or failing queries:
      unless (null (msErrors ms)) exitFailure
      unless (all snd (msQueryResults ms)) exitFailure

runArgsParser :: IO Args
runArgsParser = customExecParser (prefs showHelpOnError) argsParserInfo

argsParserInfo :: ParserInfo Args
argsParserInfo =
  info (helper <*> argsParser) . mconcat $
    [ fullDesc,
      header ("verifairy " <> gitBuildInfo),
      progDesc "Process and verify VerifPal protocols"
    ]

argsParser :: Parser Args
argsParser = Args <$> srcFileParser <*> simplify <*>verbose
  where
    verbose = flag False True . mconcat $ [ short 'v' ]
    simplify = option str (long "simplify-constant" <> short 's' <> value "")
    srcFileParser =
      strArgument . mconcat $
        [ metavar "<FILE.vp>"
        ]

commas :: [Text] -> Text
commas = Text.intercalate ", "

meh :: Text -> IO ()
meh message = do
  Text.hPutStrLn stderr message
  exitFailure
