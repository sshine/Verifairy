{-# LANGUAGE MultiParamTypeClasses #-}
module VerifPal.Pretty where

import Data.Function ((&))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void
import Error.Diagnose.Compat.Megaparsec (HasHints (hints))
import Prettyprinter (Doc (..), Pretty (..), align, annotate, colon, hardline, lbracket, rbracket, space, width, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), bold, color, colorDull, putDoc)
import Text.Show.Pretty (ppDoc)
import VerifPal.Types (Constant (..), Query (..), QueryKind (..))
import VerifPal.Check (ModelState,CanonExpr)

prettifyQuery :: QueryKind -> String
prettifyQuery (FreshnessQuery const) =
  "freshness? " ++ Text.unpack (constantName const)
prettifyQuery (EquivalenceQuery consts) =
  "equivalence? "
    ++ ( map constantName consts
           & Text.intercalate ", "
           & Text.unpack
       )
prettifyQuery k = show k

-- see: https://github.com/Mesabloo/diagnose/blob/master/test/rendering/Spec.hs
instance HasHints Void Text where
  -- hints :: Void -> [Text]
  hints _ = ["TODOwhatisthis"]

myAnnotate :: (Query, Bool) -> Doc AnsiStyle
myAnnotate (q, res) =
  let prettified :: Doc AnsiStyle
      prettified =
        pretty $ prettifyQuery $ queryKind q
   in annotate (color (if res then Green else Red)) prettified

prettifyModelState :: ModelState -> Doc AnsiStyle
prettifyModelState ms =
  pretty $ show $ ppDoc ms

prettifyCanonExpr :: CanonExpr -> Doc AnsiStyle
prettifyCanonExpr cexp =
  pretty $ show $ ppDoc cexp
