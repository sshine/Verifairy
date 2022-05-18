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
import VerifPal.Check (ModelState (..), process, canonicalizeExpr, simplifyExpr)
import VerifPal.Parser (parseModel)
import VerifPal.Pretty (myAnnotate, prettifyModelState, prettifyCanonExpr,colorYellow)--, prettifyConfidentialityGraph)
import VerifPal.Version (gitBuildInfo)
import VerifPal.Types (Constant(..), Expr(..))
import Data.Map(lookup) --lookup)
import Text.Show.Pretty (ppDoc)
import Data.GraphViz
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph (OrdGr(..) , Node)
import Data.GraphViz.Printing
import Data.GraphViz.Attributes.Complete(Justification(JLeft),Attribute(..))

data Args = Args
  { srcFile :: FilePath,
    simplify :: String,
    dotFile :: String,
    verbose :: Bool
  }
  deriving (Show)

main :: IO ()
main = runArgsParser >>= argsHandler

argsHandler :: Args -> IO ()
argsHandler Args {srcFile = srcFile, simplify=simplify, dotFile=dotFile, verbose = verbose} = do
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
      Text.hPutStrLn stderr ("Processing file " <> Text.pack srcFile)
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
             putDoc $ colorYellow "================ simplifies to -> ================"
             putStrLn ""
             putDoc (prettifyCanonExpr (simplifyExpr c_expr))
             putStrLn ""
      --
      unless (not verbose) $
        do putStrLn ""
           putDoc (prettifyModelState ms)
           putStrLn ""
      --
      --putStrLn ""
      --putDoc (prettifyConfidentialityGraph (msConfidentialityGraph ms))
      --putStrLn ""
      --
      unless (dotFile == "") $
        do Text.writeFile dotFile $ mytoDot $
             case Data.Map.lookup ("attacker"::Text) (msPrincipalConfidentialityGraph ms) of
               Just gr -> gr
               Nothing -> msConfidentialityGraph ms -- TODO allow choosing principal
      --
      -- TODO should make a Diagnostic here for each of these:
      traverse_ print (reverse $ msErrors ms)
      msQueryResults ms & map myAnnotate & for_ $ \annotated -> do
        putDoc annotated
        putStrLn ""
      -- Bail out if we have errors or failing queries:
      unless (null (msErrors ms)) exitFailure
      unless (all snd (msQueryResults ms)) exitFailure

mytoDot :: Show a => Show b => Data.Graph.Inductive.Graph.OrdGr Data.Graph.Inductive.PatriciaTree.Gr a b -> Text
mytoDot g =
  -- nodeAttrs :: (Node, Link) -> Attributes
  let edgeAttrs (x) =
        [
          toLabel . Text.pack . show $ ppDoc $ x
        ]
      nodeAttrs (a,label) = -- fmtNode= \(_,label)-> [Label (StrLabel (L.pack label))]
        [ toLabel . Text.pack . show $ ppDoc $ label
        , shape BoxShape
        , LabelJust JLeft
        , colors !! a
        --, bgColor [colors !! a]
        --fillColor [colors !! a]
        --, Style [SItem filled []]
        ]
      colors = cycle $ map bgColor [ LightBlue
                                   , Red
                                   , Orange
                                   , Yellow
                                   , Green
                                   , Blue
                                   , Purple
                                   , Brown
                                   , Pink
                                   , Gray
                                   ]
      dotgraph :: DotGraph Data.Graph.Inductive.Graph.Node
      dotgraph = case g of
        Data.Graph.Inductive.Graph.OrdGr g ->
          graphToDot (nonClusteredParams {
                         fmtNode = nodeAttrs
                         , fmtEdge = edgeAttrs
                         , globalAttributes = [
                             NodeAttrs [
                                 shape BoxShape
                                 , LabelJust JLeft -- not JCenter
                                       ]
                                            ]
                         }) g
      out :: Text
      out = Text.pack $ show $ runDotCode $ toDot dotgraph
  in out

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
argsParser = Args <$> srcFileParser <*> simplify <*> dotFile <*>verbose
  where
    verbose = flag False True . mconcat $ [ short 'v' ]
    simplify = option str (long "simplify-constant" <> short 's' <> value "")
    dotFile = option str (long "dot-file" <> value "")
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
