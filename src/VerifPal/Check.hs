
module VerifPal.Check where

import VerifPal.Types

import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data ModelError
  = OverlappingConstant Constant
  deriving (Eq, Ord, Show)

data ModelState = ModelState
  { msConstants :: Map Constant Knowledge
  , msErrors :: [ModelError]
  } deriving (Eq, Ord, Show)

emptyModelState :: ModelState
emptyModelState = ModelState
  { msConstants = Map.empty
  , msErrors = []
  }

type EvalM a = State ModelState a

-- TODO: Check if constants are unique
-- TODO: Check if a given variable is fresh

process' :: Model -> ModelState
process' model = execState (process model) emptyModelState

process :: Model -> State ModelState ()
process Model{..} =
  mapM_ processModelPart modelParts

processModelPart :: ModelPart -> State ModelState ()
processModelPart (ModelPrincipal (Principal name knows)) = do
  mapM_ processKnowledge knows

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

-- A variable is fresh if it is generated or computed using a fresh variable
--isFresh :: Knowledge -> State ModelState ()
--isFresh (
