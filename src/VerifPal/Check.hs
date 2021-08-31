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

data ModelError
  = OverlappingConstant Constant Text
  | MissingConstant Constant Text
  | NotImplemented Text
  deriving (Eq, Ord, Show)

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

processModelPart (ModelMessage (Message {..})) = do
  pure ()

processModelPart (ModelPhase (Phase {..})) = do
  pure ()

processModelPart (ModelQueries queries) = do
  mapM_ processQuery queries

processKnowledge :: PrincipalName -> (Constant, Knowledge) -> State ModelState ()
processKnowledge principalName (constant, knowledge) = do
  existingConstant <- getConstant constant
  case (existingConstant, knowledge) of
    (Nothing, Public) -> addConstant principalName constant knowledge
    (Nothing, Private) -> addConstant principalName constant knowledge
    (Nothing, Password) -> addConstant principalName constant knowledge
    (Nothing, Generates) -> addConstant principalName constant knowledge
    (Nothing, Assignment _) -> addError (NotImplemented "assignment knowledge")
    (Just _, Generates) -> addError (OverlappingConstant constant "can't generate the same thing twice")
    (Just _, Assignment _) -> addError (OverlappingConstant constant "can't assign to the same name twice")
    (_, Leaks) -> modifyConstant principalName constant Leaks
    (Just existingKnowledge, _) ->
      if existingKnowledge == knowledge
      then upsertPrincipalConstant principalName constant knowledge
      else addError (OverlappingConstant constant "can't generate the same thing twice")

processQuery :: Query -> State ModelState ()
processQuery query@(Query (FreshnessQuery constant) queryOptions) = do
  knowledge <- getConstant constant
  case knowledge of
    Nothing -> addError (MissingConstant constant "herp derp")
    Just knowledge -> addQueryResult query (knowledge == Generates)

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

processKnowledge :: (Constant, Knowledge) -> State ModelState ()
processKnowledge (constant, knowledge) = do
  constants <- gets msConstants
  case (knowledge, Map.lookup constant constants) of
    ( Public, Just (Public)) -> modify (\st -> st)
    ( Password, Just (Password)) -> modify (\st -> st)
    ( Private, Just (Private)) -> modify (\st -> st)
    (_, Just Leaks) -> modify (\st -> st)
    (Leaks, Just (_)) -> modify (\st -> st { msConstants = Map.insert constant knowledge constants } )
    (_, Nothing) -> modify (\st -> st { msConstants = Map.insert constant knowledge constants })
    (_, Just _) -> addError (OverlappingConstant constant)

addError :: ModelError -> State ModelState ()
addError err = modify (\st -> st { msErrors = err : msErrors st })
