module Main where

import Control.Monad (unless)
import Data.Foldable (for_, traverse_)
import Data.Function ((&))
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Text.Lazy as Text.Lazy
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
import Data.GraphViz.Attributes.Complete(Justification(JLeft),Attribute(..), EdgeType(..), Overlap(..))

data Args = Args
  { srcFile :: FilePath,
    simplify :: String,
    dotFile :: String,
    verbose :: Bool,
    ignore_constraints :: Bool
  }
  deriving (Show)

main :: IO ()
main = runArgsParser >>= argsHandler

argsHandler :: Args -> IO ()
argsHandler Args {srcFile = srcFile
                 , simplify=simplify
                 , dotFile=dotFile
                 , ignore_constraints = ignore_constraints
                 , verbose = verbose} = do
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
      unless (not verbose) $
        do putStrLn ""
           putDoc (prettifyModelState ms)
           putStrLn ""
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
      unless (ignore_constraints || all snd (msQueryResults ms)) exitFailure

mytoDot :: Show a => Show b => Data.Graph.Inductive.Graph.OrdGr Data.Graph.Inductive.PatriciaTree.Gr a (Set (Set b)) -> Text
mytoDot g =
  -- TODO it would be nice to strip back arrows before emitting this graph
  -- nodeAttrs :: (Node, Link) -> Attributes
  -- https://graphviz.org/docs/attrs/stylesheet/ url to a stylesheet
  -- https://graphviz.org/docs/attrs/tooltip/
  -- https://graphviz.org/docs/attrs/xlabel/
  -- https://graphviz.org/docs/outputs/vrml/ protocol analysis in 3D!
  -- Root True on "attacker" node
  let fixAlign :: Text -> Text
      fixAlign text =
        -- \l left-justifies the current line (as opposed to \n which centers)
        Text.replace "\n" "\\l" . flip Text.append "\\l" $ text
      ppEdge (_from,_to,s) =
        let treated = if all null s then "" else show $ ppDoc s
        in fixAlign $ Text.pack treated
      edgeAttrs x@(from,to,_label) =
        [
          toLabel $ ppEdge x
        , colors !! (from+to)
        , Decorate True
        ]
      nodeAttrs (a,label) = -- fmtNode= \(_,label)-> [Label (StrLabel (L.pack label))]
        [ toLabel . fixAlign . Text.pack . show $ ppDoc $ label
        --, LabelTarget "a"
        --, LabelURL "b"
        --, LabelTooltip "foo"
        , Tooltip $ Text.Lazy.fromStrict $Text.pack $ show a
        , URL "javascript:alert(3)"
        --, colors !! a
        , Data.GraphViz.style filled
        --, bgColor [colors !! a]
        --fillColor [colors !! a]
        --, Style [SItem filled []]
        ]
      colors = cycle $ map color [ LightBlue
                                   , Red
                                   , Orange
                                   --, Yellow
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
                             EdgeAttrs [
                                 FontName "Mono"
                                 , color Firebrick1 --(RGB 0xfe 0x4a 0x49) -- ofc this is broken in haskell, but https://graphviz.org/doc/info/colors.html#brewer lists a bunch of the colors that actually work in this library
                                 --, Constraint False
                                 -- TODO if we use records we can have "ports" so
                                 -- we can draw lines accurately from each argument
                                 -- https://hackage.haskell.org/package/graphviz-2999.18.1.2/docs/src/Data-GraphViz-Attributes-Values.html#RecordField
                                       ],
                             GraphAttrs [
                                 Splines Ortho
--  data EdgeType
--  = SplineEdges | LineEdges | NoEdges | PolyLine | Ortho | Curved | CompoundEdge
                                 , Overlap $ PrismOverlap Nothing
                                        ],
                             NodeAttrs [
                                 shape BoxShape
                                 , NoJustify True
                                 , shape BoxShape
                                 , Group "hello"
                                 , FontName "Mono"
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
argsParser = Args <$> srcFileParser <*> simplify <*> dotFile <*> verbose <*> ignore_constraints
  where
    verbose = flag False True . mconcat $ [
      short 'v' <> help "be (extremely) verbose"
      ]
    ignore_constraints = flag False True . mconcat $ [
      short 'i' <>
      help "exit code 0 even with failed constraints. useful with --dot-file"
      ]
    simplify = option str (
      long "simplify-constant" <> short 's' <> value "" <>
        help "shows the named constant in minimal equivalent form" <>
        metavar "CONSTANT"
                          )
    dotFile = option str (long "dot-file" <> value "" <>
                          help "outputs a 'dot'/graphviz file: '--dot-file x.dot ; dot x.dot -Tsvg -o x.svg'")
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
