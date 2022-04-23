{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module VerifPal.Check where

import VerifPal.Types

import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)

--import Data.Graph.Inductive.Graph (mkGraph, LNode, LEdge, OrdGr, DynGraph, empty, Graph)
--import Data.Graph.Inductive.PatriciaTree

data ModelError
  = OverlappingConstant Constant Text
  | MissingConstant Constant Text
  | NotImplemented Text
  deriving (Eq, Ord, Show)

-- graph mapping constants to the expressions that *directly* contain them
-- expressions are either obtained
--
-- attacker obtains constants either through:
-- Knowledge Leaks
-- Message Constant where
--   msConstants[Constant] =
--     ( (Assignment Expr)) that can be unlocked
type KTree =
  Map Constant [Knowledge]

data ModelState = ModelState
  { msConstants          :: Map Constant Knowledge
  , msPrincipalConstants :: Map PrincipalName (Map Constant (Knowledge, ProcessingCounter))
  , msProcessingCounter  :: ProcessingCounter
  , msErrors             :: [ModelError]
  , msQueryResults       :: [(Query, Bool)]
  } deriving (Eq, Ord, Show)

type ProcessingCounter = Int

emptyModelState :: ModelState
emptyModelState = ModelState
  { msConstants = Map.empty
  , msPrincipalConstants = Map.empty
  , msProcessingCounter = 0
  , msErrors = []
  , msQueryResults = []
  }

type EvalM a = State ModelState a

-- TODO: Check if constants are unique
-- TODO: Check if a given variable is fresh

process :: Model -> ModelState
process model = execState (processM model) emptyModelState

processM :: Model -> State ModelState ()
processM Model{..} =
  mapM_ processModelPart modelParts

processModelPart :: ModelPart -> State ModelState ()
processModelPart (ModelPrincipal (Principal name knows)) = do
  mapM_ (processKnowledge name) knows
processModelPart (ModelQueries qs) = do
  -- TODO if the user wrote the same query twice
  -- we should collapse them to a single query
  -- and probably issue a warning?
  mapM_ processQuery qs

processModelPart (ModelMessage (Message sender receiver consts)) = do
  forM_ consts $ \(cconst,cguard) -> do
    -- check the sender knows all the constants being sent:
    hasPrincipalConstantOrError sender cconst "sender reference to unknown constant"
    -- add them to the knowledge of the receiver so they know them too:
    maybeknowledge <- getConstant cconst
    case maybeknowledge of
      Nothing -> pure ()
      Just knowledge -> upsertPrincipalConstant receiver cconst knowledge
    -- TODO add consts to attacker knowledge

processModelPart (ModelPhase (Phase {..})) = do
  pure ()

processKnowledge :: PrincipalName -> (Constant, Knowledge) -> State ModelState ()
processKnowledge principalName (constant, knowledge) = do
  -- we need to consider three "knowledges":
  -- 1) does it exist anywhere
  -- 2) does this principal know about it
  -- 3) does the attacker know about it?
  existingConstant <- getConstant constant
  case (existingConstant, knowledge) of
    (Nothing, Public) -> addConstant principalName constant knowledge
    (Nothing, Private) -> addConstant principalName constant knowledge
    (Nothing, Password) -> addConstant principalName constant knowledge
    (Nothing, Generates) -> addConstant principalName constant knowledge
    (Nothing, Assignment exp) ->
      -- For assignments we check that all the referenced constants exist
      -- in the knowledge map associated with the current principal.
      -- The ambition is to catch both references to undefined constants (typos)
      -- and cases where a reference is made to a constant that exists, but it isn't
      -- known by (principalName):
      foldConstantsInExpr (addConstant principalName constant knowledge)
      exp (\c st -> do
         st >>= pure (hasPrincipalConstantOrError principalName c "assignment to unbound constant")
      )
    (Just _, Generates) -> addError (OverlappingConstant constant "can't generate the same thing twice")
    (Just _, Assignment _) -> addError (OverlappingConstant constant "can't assign to the same name twice")
    (_, Leaks) ->
      -- TODO give it to the attacker
      modifyConstant principalName constant Leaks
    (Just existingKnowledge, _) ->
      if existingKnowledge == knowledge
      then upsertPrincipalConstant principalName constant knowledge
      else addError (OverlappingConstant constant "can't generate the same thing twice")

processQuery :: Query -> State ModelState ()
processQuery query@(Query (FreshnessQuery constant) queryOptions) = do
  constantExistsOrError constant
  cs <- gets msConstants ;
  addQueryResult query $ mapConstants False constant (
    \c a -> a || Just Generates == Map.lookup c cs) cs

processQuery (Query (ConfidentialityQuery constant) queryOptions) = do
  addError (NotImplemented "confidentiality query not implemented") -- FIXME

getConstant :: Constant -> State ModelState (Maybe Knowledge)
getConstant constant = gets $ Map.lookup constant . msConstants

canOverlap :: Knowledge -> Bool
canOverlap = \case
  Private -> True
  Public -> True
  Password -> True
  Leaks -> True
  Generates -> False
  Assignment _ -> False

addQueryResult :: Query -> Bool -> State ModelState ()
addQueryResult query result = modify $ \state ->
  state { msQueryResults = msQueryResults state <> [(query, result)] }

hasConstant :: Constant -> Knowledge -> State ModelState Bool
hasConstant constant knows1 = do
  knows2 <- getConstant constant
  pure (Just knows1 == knows2)

hasPrincipalConstant :: PrincipalName -> Constant -> State ModelState Bool
hasPrincipalConstant principalName constant = do
  currentCount <- getCounter
  principalMap <- gets (fromMaybe Map.empty . Map.lookup principalName . msPrincipalConstants)
  case Map.lookup constant principalMap of
    Just (know, cou) | cou <= currentCount -> pure True
    Just _ -> pure False -- not yet
    Nothing -> pure False

hasPrincipalConstantOrError :: PrincipalName -> Constant -> Text -> State ModelState ()
hasPrincipalConstantOrError principalName refconstant errorText = do
  (\() ->
     do xy <- hasPrincipalConstant principalName refconstant
        if xy
          then pure ()
          else addError (MissingConstant refconstant errorText)) ()

addConstant :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
addConstant principalName constant knowledge = do
  existingConstant <- gets (Map.lookup constant . msConstants)
  case existingConstant of
    Just _ -> addError (OverlappingConstant constant "constant already defined")
    Nothing -> do
      upsertConstantBoth principalName constant knowledge

modifyConstant :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
modifyConstant principalName constant knowledge = do
  existingConstant <- gets (Map.lookup constant . msConstants)
  case existingConstant of
    Nothing -> addError (MissingConstant constant "Can't modify non-existent constant")
    Just _ -> upsertConstantBoth principalName constant knowledge

upsertConstantBoth :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
upsertConstantBoth principalName constant knowledge = do
  upsertConstant constant knowledge
  upsertPrincipalConstant principalName constant knowledge

upsertConstant :: Constant -> Knowledge -> State ModelState ()
upsertConstant constant knowledge =
  modify $ \state -> state { msConstants = Map.insert constant knowledge (msConstants state) }

upsertPrincipalConstant :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
upsertPrincipalConstant principalName constant knowledge = do
  count <- getCounter
  principalMap <- gets (fromMaybe Map.empty . Map.lookup principalName . msPrincipalConstants)
  let newPrincipalMap = Map.insert constant (knowledge, count) principalMap
  modify $ \state -> state { msPrincipalConstants = Map.insert principalName newPrincipalMap (msPrincipalConstants state) }

getCounter :: State ModelState ProcessingCounter
getCounter = do
  count <- gets msProcessingCounter
  modify (\st -> st { msProcessingCounter = count + 1 })
  pure count

-- note that this ONLY folds over the constants in an expression,
-- NOT the knowledge maps, so it will not "jump" across maps of knowledge
-- from other principals.
foldConstantsInExpr :: acc -> Expr -> (Constant -> acc -> acc) -> acc
foldConstantsInExpr acc o_exp f =
  let dolist = foldl (\acc exp -> foldConstantsInExpr acc exp f) acc in
  case o_exp of
    G exp -> dolist [exp]
    (:^:) c exp -> foldConstantsInExpr (f c acc) exp f
    EConstant c -> f c acc
    EPrimitive prim _ ->
      case prim of
        ASSERT e1 e2 -> dolist [e1, e2]
        CONCAT exps -> dolist exps
        SPLIT exp -> dolist [exp]
        HASH exps -> dolist exps
        MAC e1 e2 -> dolist [e1, e2]
        HKDF e1 e2 e3 -> dolist [e1, e2, e3]
        PW_HASH exps -> dolist exps
        ENC e1 e2 -> dolist [e1, e2]
        DEC e1 e2 -> dolist [e1, e2]
        AEAD_ENC e1 e2 e3 -> dolist [e1, e2, e3]
        AEAD_DEC e1 e2 e3 -> dolist [e1, e2, e3]
        PKE_ENC e1 e2 -> dolist [e1, e2]
        PKE_DEC e1 e2 -> dolist [e1, e2]
        SIGN e1 e2 -> dolist [e1, e2]
        SIGNVERIF e1 e2 e3 -> dolist [e1, e2, e3]
        RINGSIGN e1 e2 e3 e4 -> dolist [e1, e2, e3, e4]
        RINGSIGNVERIF e1 e2 e3 e4 e5 -> dolist [e1, e2, e3, e4, e5]
        BLIND e1 e2 -> dolist [e1, e2]
        UNBLIND e1 e2 e3 -> dolist [e1, e2, e3]
        SHAMIR_SPLIT e1 -> dolist [e1]
        SHAMIR_JOIN e1 e2 e3 -> dolist [e1, e2, e3]

-- note that this can call f with the same constant
-- several times:
mapConstants :: a -> Constant -> (Constant -> a -> a) -> Map Constant Knowledge -> a
mapConstants acc c f m =
  case Map.lookup c m of
    Nothing -> acc
    Just vals ->
      case vals of
        Assignment exp ->
          foldConstantsInExpr (f c acc) exp (\c a -> mapConstants a c f m)
        Leaks -> f c acc
        Password -> f c acc
        Received _ -> f c acc
        Generates -> f c acc
        Public -> f c acc
        Private -> f c acc

addError :: ModelError -> State ModelState ()
addError err = modify (\st -> st { msErrors = err : msErrors st })

constantExistsOrError :: Constant -> State ModelState ()
constantExistsOrError const = do
  seen <- getConstant const ;
  case seen of
    Just _ -> return ()
    Nothing -> addError (MissingConstant const "TODO")
