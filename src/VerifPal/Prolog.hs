module VerifPal.Prolog where

import VerifPal.Types
import VerifPal.Check
--import Data.Text
import qualified Data.Text
import qualified Data.List.NonEmpty
import Data.List
import Control.Monad

primitiveToProlog :: PrimitiveP String -> String
primitiveToProlog p =
  case p of
    HASH exps -> "p_hash([" ++ (Data.List.intercalate "," exps) ++"])"
    PW_HASH exps -> "p_pwhash([" ++ (Data.List.intercalate "," exps) ++"])"
    ENC e1 e2 -> "p_enc([" ++ (Data.List.intercalate "," [e1,e2]) ++"])"
    DEC e1 e2 -> "p_dec([" ++ (Data.List.intercalate "," [e1,e2]) ++"])"

exprToProlog :: Expr -> String
exprToProlog cexpr =
  case cexpr of
    EConstant (Constant x) -> Data.Text.unpack x
    G x -> "p_G(" ++ (exprToProlog x) ++ ")"
    EPrimitive p _ -> primitiveToProlog $ mapPrimitiveP p exprToProlog

modelQueryToProlog :: Query -> [String]
modelQueryToProlog (Query (ConfidentialityQuery (Constant c)) _) =
  ["confidentiality(" ++ (Data.Text.unpack c) ++ ")"]

modelPartToProlog :: ModelPart -> [String]
modelPartToProlog (ModelPrincipal (Principal pNameText pKnows)) =
  let pName = "principal_" ++ (Data.Text.unpack pNameText)
      folded :: [String]
      folded =
        foldl' (
        \acc (cs, knowledge) ->
          case Data.List.NonEmpty.uncons cs of
            (Constant lhs_text, Nothing) ->
              let lhs = Data.Text.unpack lhs_text
                  out = case knowledge of
                    Password -> ("knows_password("++ pName ++ "," ++ lhs ++")")
                    Private -> ("knows_private("++ pName ++ "," ++ lhs ++")")
                    Public -> ("knows_public("++ pName ++ "," ++ lhs ++")")
                    Generates -> ("knows_generates("++ pName ++ "," ++ lhs ++")")
                    Leaks -> ("leaks("++ pName ++ "," ++ lhs ++")")
                    Assignment expr ->
                      let prologExpr = exprToProlog expr
                      in ("knows_private(" ++ pName ++ "," ++ prologExpr ++ ")")
              in out:acc
            --(_, Just _)
            -- | Data.List.elem knowledge [Private,Public,Generates,Leaks] ->
            --   fold over cs and generate separate statements :acc
        ) ["principal(" ++ pName ++ ")"] pKnows
  in Data.List.reverse folded

modelPartToProlog (ModelMessage (Message a b m)) =
  ["% ModelMessage not implemented"]

modelPartToProlog (ModelPhase (Phase phase)) =
  ["% phase " ++ show phase]

modelPartToProlog (ModelQueries qs) =
  foldl (\acc q -> acc ++ modelQueryToProlog q) [] qs

toProlog :: Model -> String
toProlog (Model { modelAttacker = attackerKind,
                  modelParts = parts
                }) =
  let attackerList =
        "principal(attacker)" : (
        case attackerKind of
          Active -> ["% attacker[active]"::String]
          Passive -> ["% attacker[passive]"])
      --partList <- foldl (\acc b -> b:acc) [] $
      partList :: [String]
      partList = foldl' (\acc b -> acc ++ (modelPartToProlog b)) []  parts
      complete :: [[Char]]
      complete = attackerList ++ partList
      between :: [Char]
      between = ".\n"
      out = Data.List.intercalate between (complete ++ [""])
  in out
