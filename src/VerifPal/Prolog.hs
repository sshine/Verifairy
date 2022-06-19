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
    CONCAT exps -> "p_concat([" ++ (Data.List.intercalate "," exps) ++ "])"
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
      basic knowledge lhs =
        case knowledge of
          Password -> ("knows_password("++ pName ++ "," ++ lhs ++")")
          Private -> ("knows_private("++ pName ++ "," ++ lhs ++")")
          Public -> ("knows_public("++ pName ++ "," ++ lhs ++")")
          Generates -> ("knows_generates("++ pName ++ "," ++ lhs ++")")
          Leaks -> ("leaks("++ pName ++ "," ++ lhs ++")")
          Assignment expr ->
            let prologExpr = exprToProlog expr
            in ("knows_assignment(" ++ pName ++ "," ++ lhs ++
                 "," ++ prologExpr ++ ")")
      folded :: [String]
      folded =
        foldl' (
        \acc (cs, knowledge) ->
          case Data.List.NonEmpty.uncons cs of
            (Constant lhs_text, Nothing) ->
              let lhs = Data.Text.unpack lhs_text
                  out = basic knowledge lhs
              in out:acc
            (Constant _, Just _) ->
              let f =
                    Data.List.reverse $
                    Data.List.NonEmpty.toList $
                    Data.List.NonEmpty.map (
                    \(Constant lhs) -> basic knowledge (
                      Data.Text.unpack lhs)) cs
              in
                case knowledge of
                  --   fold over cs and generate separate statements :acc
                  Private -> f ++ acc
                  Public -> f ++ acc
                  Generates -> f ++ acc
                  Leaks -> f ++ acc
                  Password -> f ++ acc
                  Assignment _ -> f ++ acc -- should be a fold generating item(0, ...)
                  Received _ -> acc -- ignored, the Message should suffice.
        ) ["principal(" ++ pName ++ ")"] pKnows
  in Data.List.reverse folded

modelPartToProlog (ModelMessage (Message a b msgs)) =
  --["% ModelMessage not implemented"]
  map
  (\(Constant const, guarded) ->
     "message(" ++ (Data.Text.unpack a) ++ ", " ++
     (Data.Text.unpack b) ++ ", " ++ (Data.Text.unpack const) ++
     ", " ++ (if guarded
              then "true"
              else "false") ++ ")"
  ) msgs

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
