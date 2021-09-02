
module VerifPal.Check where

import VerifPal.Types

import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

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

process :: Model -> ModelState
process model = execState (processM model) emptyModelState

processM :: Model -> State ModelState ()
processM Model{..} =
  mapM_ processModelPart modelParts

processModelPart :: ModelPart -> State ModelState ()
processModelPart (ModelPrincipal (Principal name knows)) = do
  mapM_ (processKnowledge name) knows

processKnowledge :: PrincipalName -> (Constant, Knowledge) -> State ModelState ()
processKnowledge _principalName (constant, knowledge) = do
  hasOverlappingConstant <- hasConstant constant
  if hasOverlappingConstant
    then addError (OverlappingConstant constant)
    else addConstant constant knowledge

getConstant :: Constant -> State ModelState (Maybe Knowledge)
getConstant constant = gets $ Map.lookup constant . msConstants

hasConstant :: Constant -> State ModelState Bool
hasConstant = fmap isJust . getConstant

addConstant :: Constant -> Knowledge -> State ModelState ()
addConstant constant knowledge = modify $ \state ->
  state { msConstants = Map.insert constant knowledge (msConstants state) }

addError :: ModelError -> State ModelState ()
addError err = modify (\st -> st { msErrors = err : msErrors st })

-- A variable is fresh if it is generated or computed using a fresh variable
--isFresh :: Knowledge -> State ModelState ()
--isFresh (
