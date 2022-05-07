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
import Data.Graph.Inductive
import Data.List
import Data.List.NonEmpty

--import Data.Graph.Inductive.Graph (mkGraph, LNode, LEdge, OrdGr, DynGraph, empty, Graph)
--import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.TransClos

data ModelError
  = OverlappingConstant Constant
  | MissingConstant Constant
  | ValueToValue Constant Constant
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

data ModelState = ModelState
  { msConstants          :: Map Constant Knowledge
  , msPrincipalConstants :: Map PrincipalName (Map Constant (Knowledge, ProcessingCounter))
  , msProcessingCounter  :: ProcessingCounter
  , msErrors             :: [ModelError]
  , msQueryResults       :: [(Query, Bool)]
  } deriving (Eq, Ord, Show)

type ProcessingCounter = Int

-- Everyone knows the magic constant "nil" TODO reference manual?
emptyConstantMap :: Map Constant Knowledge
emptyConstantMap = Map.fromList [
  (Constant {constantName="nil"}, Public)
  ]
emptyPrincipalConstantMap :: Map Constant (Knowledge, ProcessingCounter)
emptyPrincipalConstantMap = Map.fromList [
  (Constant {constantName="nil"}, (Public,0))
  ]

emptyModelState :: ModelState
emptyModelState = ModelState
  { msConstants = emptyConstantMap
  , msPrincipalConstants = Map.empty
  , msProcessingCounter = 0
  , msErrors = []
  , msQueryResults = []
  }

type EvalM a = State ModelState a

-- TODO: Check if constants are unique
-- TODO: Check if a given variable is fresh

buildKnowledgeGraph :: ModelState -> Bool
buildKnowledgeGraph m =
  let vertices = [] :: [(Node, Int)]
      edges = []  :: [LEdge Int]
      g = mkGraph (vertices) (edges) :: Gr Int Int
      -- compute transitive reflexive closure aka compute reachability for each vertice pair:
      gtrc = Data.Graph.Inductive.Query.TransClos.trc g
      -- shortest path: Data.Graph.Inductive.Query.SP
  in
    True
process :: Model -> ModelState
process model = do
  let m = execState (processM model) emptyModelState
      _ = buildKnowledgeGraph m
  m

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
  forM_ consts $ \(cconst,_TODO_cguard) -> do
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

processAssignment :: PrincipalName -> NonEmpty Constant -> Expr -> State ModelState ()
processAssignment principalName lhs expr = do
  -- For assignments we check that all the referenced constants exist
  -- in the knowledge map associated with the current principal.
  -- The ambition is to catch both references to undefined constants (typos)
  -- and cases where a reference is made to a constant that exists, but it isn't
  -- known by (principalName):

  -- TODO FIXME
  --if constant == Constant{constantName="_"}
  --then pure ()

  -- Check that all referenced constants in rhs are known to this principal:
  foldConstantsInExpr (pure())
    expr (\c st -> do
             st >>= pure (hasPrincipalConstantOrError principalName c "assignment to unbound constant")
          )
  --
  prMap <- gets (fromMaybe emptyPrincipalConstantMap . Map.lookup principalName . msPrincipalConstants)
  -- TODO let simple_cexpr = simplifyExpr $ canonicalizeExpr (Map.map fst prMap) expr
  let simple_cexpr = canonicalizeExpr (Map.map fst prMap) expr
      constr ctr = do
        case simple_cexpr of
          CPrimitive (SPLIT {}) _ -> EItem ctr expr
          CPrimitive (HKDF {}) _ -> EItem ctr expr
          CPrimitive (SHAMIR_SPLIT {}) _ -> EItem ctr expr
          _ -> expr
  foldM (
    \ctr constant ->
      do
        if "_" == constantName constant -- these are wildcards / discarded
          then pure ()
          else addConstant principalName constant (Assignment $ constr ctr)
        pure (ctr + 1)
    ) 0 lhs >>= \n -> let _ = n :: Int in pure ()

processKnowledge :: PrincipalName -> (NonEmpty Constant, Knowledge) -> State ModelState ()
processKnowledge principalName (constants, knowledge) = do
  -- we need to consider three "knowledges":
  -- 1) does it exist anywhere
  -- 2) does this principal know about it
  -- 3) does the attacker know about it?
  --
  -- First check that lhs is unique or "_":
  foldM_ (
    \acc constant ->
      if constantName constant == "_"
      then pure ()
      else do
        existingConstant <- getConstant constant
        case existingConstant of
          Nothing -> pure ()
          -- TODO cannot be "leaks"
          Just Password -> pure ()
          Just Private -> pure ()
          Just Public -> pure ()
          Just Generates -> addError (OverlappingConstant constant)
          Just (Assignment {}) -> addError (OverlappingConstant constant)
    ) () constants
  let addThem () = foldM_ (
        \() constant -> do
          existingConstant <- getConstant constant
          case (existingConstant, knowledge) of
            (Nothing, _) -> addConstant principalName constant knowledge
            -- principal A [ knows public x ] principal B [ knows public X ]
            (Just Public, Public) -> upsertPrincipalConstant principalName constant knowledge
            (Just Private, Private) -> upsertPrincipalConstant principalName constant knowledge
            (Just Password, Password) -> upsertPrincipalConstant principalName constant knowledge
            (Just _, _) -> addError (OverlappingConstant constant)
        ) () constants
  case knowledge of
    Assignment (EConstant rhs) -> addError $ ValueToValue (Data.List.NonEmpty.head constants) rhs
    Assignment exp -> processAssignment principalName constants exp
    Public -> addThem ()
    Private -> addThem ()
    Password -> addThem ()
    Generates -> addThem ()
    Leaks -> pure () -- TODO add to attacker principal modifyConstant principalName constant Leaks

processQuery :: Query -> State ModelState ()
processQuery query@(Query (FreshnessQuery constant) queryOptions) = do
  constantExistsOrError constant
  cs <- gets msConstants ;
  addQueryResult query $ mapConstants False constant (
    \c a -> a || Just Generates == Map.lookup c cs) cs

processQuery (Query (ConfidentialityQuery constant) queryOptions) = do
  constantExistsOrError constant
  addError (NotImplemented "confidentiality query not implemented") -- FIXME

processQuery (Query (UnlinkabilityQuery consts) queryOptions) = do
  forM_ consts $ \cconst -> do constantExistsOrError cconst
  addError (NotImplemented "unlinkability query not implemented") -- FIXME

processQuery (Query (AuthenticationQuery msg) queryOptions) = do
  addError (NotImplemented "authentication query not implemented") -- FIXME

processQuery (Query (EquivalenceQuery []) _queryOptions) = pure ()

processQuery query@(Query (EquivalenceQuery consts@(c1:cs)) queryOptions) = do
  forM_ consts $ \cconst -> do
    constantExistsOrError cconst
  constmap <- gets msConstants ;
  let (_, result) = (foldl (\(c1,result) c2 ->
                              let x2 = canonicalizeExpr constmap (EConstant c2) in
                                (c1, result && equivalenceExpr c1 x2)
                           )(canonicalizeExpr constmap (EConstant (c1)), True) consts)
    in
    addQueryResult query $ result

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
  principalMap <- gets (fromMaybe emptyPrincipalConstantMap . Map.lookup principalName . msPrincipalConstants)
  case Map.lookup constant principalMap of
    Just (_know, cou) | cou <= currentCount -> pure True
    Just _ -> pure False -- not yet
    Nothing -> pure False

hasPrincipalConstantOrError :: PrincipalName -> Constant -> Text -> State ModelState ()
hasPrincipalConstantOrError principalName refconstant errorText = do
  (\() ->
     do xy <- hasPrincipalConstant principalName refconstant
        if xy
          then pure ()
          else addError (MissingConstant refconstant)) ()

addConstant :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
addConstant principalName constant knowledge = do
  existingConstant <- gets (Map.lookup constant . msConstants)
  case existingConstant of
    Just _ -> addError (OverlappingConstant constant)
    Nothing -> do
      upsertConstantBoth principalName constant knowledge

modifyConstant :: PrincipalName -> Constant -> Knowledge -> State ModelState ()
modifyConstant principalName constant knowledge = do
  existingConstant <- gets (Map.lookup constant . msConstants)
  case existingConstant of
    Nothing -> addError (MissingConstant constant)
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
  principalMap <- gets (fromMaybe emptyPrincipalConstantMap . Map.lookup principalName . msPrincipalConstants)
  let newPrincipalMap = Map.insert constant (knowledge, count) principalMap
  modify $ \state -> state { msPrincipalConstants = Map.insert principalName newPrincipalMap (msPrincipalConstants state) }

getCounter :: State ModelState ProcessingCounter
getCounter = do
  count <- gets msProcessingCounter
  modify (\st -> st { msProcessingCounter = count + 1 })
  pure count

quicksort :: Ord a => [a] -> [a]
quicksort []     = []
quicksort (p:xs) = (quicksort lesser) ++ [p] ++ (quicksort greater)
    where
        lesser  = Prelude.filter (< p) xs
        greater = Prelude.filter (>= p) xs
-- equationToList is a sorted list of the expressions that constitute
-- the terms of an expression.
-- The idea is that G^x^y^z should give [x,y,z]
--              and G^z^y^x should give [x,y,z]
equationToList :: [CanonExpr] -> CanonExpr -> [CanonExpr]
equationToList acc c =
  case simplifyExpr c of
    -- special case: G^base^b: we strip the base TODO this is no good
    -- TODO because it may be DEC(x,ENC(x, G base)) which is also ok.
    --((:^^:) (CG base) (CG b)) -> equationToList (base:acc) b
    --((:^^:) base (CG b)) ->
      --quicksort (base : (map CG (equationToList [] b)) ++ acc)
    --((:^^:) (CG base) b) -> equationToList (base:acc) b
    -- x^y: recurse to see if x or y are themselves :^^:
    ((:^^:) lhs rhs) ->
      equationToList (equationToList acc lhs) rhs
    CG term | acc == [] -> -- innermost lhs should be CG (TODO typecheck that)
      quicksort (term:acc)
    -- term was not :^^: so it's just a term:
    term -> quicksort (term:acc)

simplifyExpr' :: Bool -> CanonExpr -> CanonExpr
simplifyExpr' skipPrimitive e = do
  case e of
    CPrimitive (SPLIT (CPrimitive (CONCAT (hd:_)) _)) _
      | not skipPrimitive -> simplifyExpr hd -- TODO is it correct to throw away the rest?
    --CPrimitive (CONCAT [
    --               CPrimitive (SPLIT
    --                           (CPrimitive (CONCAT lst) _TODOhasq)
    --                          ) _
    --                   ]) hasq -> CPrimitive (CONCAT lst) hasq
    -- TODO SHAMIR_JOIN(SHAMIR_SPLIT)
    -- UNBLIND(k, m, SIGN(a, BLIND(k, m))): SIGN(a, m)
    CPrimitive (UNBLIND k m (CPrimitive (SIGN a (CPrimitive (BLIND k2 m2) hasq'')) hasq')) hasq
      | not skipPrimitive -> do
      let s_k = simplifyExpr k
          s_m = simplifyExpr m
          s_a = simplifyExpr a
          s_k2 = simplifyExpr k2
          s_m2 = simplifyExpr m2
      if (equivalenceExpr s_k s_k2) && (equivalenceExpr s_m s_m2)
      then (CPrimitive (SIGN s_a s_m) hasq)
      else (CPrimitive (UNBLIND s_k s_m (CPrimitive (SIGN s_a (CPrimitive (BLIND s_k2 s_m2) hasq'')) hasq')) hasq)
    -- SIGNVERIF(G^k,m,SIGN(k,m)) -> m
    CPrimitive (SIGNVERIF g_key message (CPrimitive (SIGN key message') hasq')) hasq
      | not skipPrimitive -> do
      let simple_g_key = simplifyExpr g_key
          simple_key = simplifyExpr key
          simple_message = simplifyExpr message
          simple_message' = simplifyExpr message'
      if (equivalenceExpr simple_g_key (CG simple_key) &&
          equivalenceExpr simple_message simple_message')
         then simple_message
         else (CPrimitive (SIGNVERIF simple_g_key simple_message (CPrimitive (SIGN simple_key simple_message') hasq')) hasq)

    -- DEC(k, ENC(k, payload)) -> payload
    CPrimitive (DEC key encrypted) hasq | not skipPrimitive -> do
      let simple_enc = simplifyExpr encrypted
          simple_key = simplifyExpr key
      case simple_enc of
        -- remove the key:
        CPrimitive (ENC simple_key' payload) _
          | equivalenceExpr simple_key simple_key' -> simplifyExpr payload
        _ -> CPrimitive (DEC simple_key simple_enc) hasq
    -- AEAD_DEC(k, AEAD_ENC(k, payload, ad), ad) -> payload
    CPrimitive (AEAD_DEC key encrypted ad) hasq
      | not skipPrimitive-> do
      let simple_enc = simplifyExpr encrypted
          simple_key = simplifyExpr key
          simple_ad  = simplifyExpr ad
      case simple_enc of
        -- remove the dec(enc()) if key and ad match:
        CPrimitive (AEAD_ENC simple_key' payload simple_ad') _
          | equivalenceExpr simple_key simple_key' && equivalenceExpr simple_ad simple_ad' -> simplifyExpr payload
        _ -> CPrimitive (AEAD_DEC simple_key simple_enc simple_ad) hasq
    -- TODO may need: CPrimitive ep hasq -> CPrimitive (mapPrimitiveP ep simplifyExpr) hasq
    CPrimitive p hq | skipPrimitive -> simplifyExpr' False (CPrimitive (mapPrimitiveP p (simplifyExpr)) hq)
    CPrimitive p hq -> CPrimitive p hq
    CItem idx old_e -> do
      let simple_e = simplifyExpr old_e
          default_item = CItem idx simple_e
          get_item lst = case Data.List.drop idx lst of
                           [] -> default_item -- TODO this is a type error we should have caught earlier
                           new_e:_ -> new_e
      case old_e of
        CPrimitive (SPLIT inner) _ -> do
           let simple_inner = simplifyExpr inner
           case simple_inner of
             (CPrimitive (CONCAT lst) _) -> simplifyExpr (get_item lst)
             _ -> default_item
        _ -> default_item
    CG e -> CG (simplifyExpr' skipPrimitive e)
    (:^^:) a b -> (:^^:) (simplifyExpr a) (simplifyExpr b)
    e@(CConstant {}) -> e
simplifyExpr :: CanonExpr -> CanonExpr
simplifyExpr e =
  simplifyExpr' True e
equivalenceExpr' :: CanonExpr -> CanonExpr -> Bool
equivalenceExpr' o_e1 o_e2 =
  -- TODO it might be nice to memoize the results of these comparisons
  -- in a set in the future
  case (simplifyExpr o_e1, simplifyExpr o_e2) of
    -- Equations are kind of tricky:
    -- it needs to hold that G^a^x^y^z === G^z^a^y^x etc,
    -- the approach taken here is to sort the expressions (using Ord or whatever)
    -- and then compare them term by term:
    --
    --
    (CConstant c _, CConstant c' _) -> c == c'
    -- Below we have some transformations, they are all guarded to avoid shorting
    -- the match cases when they don't match.
    -- TODO it might be a better strategy to have a "minimizeExpr" function to do
    -- these; then we could reuse that to e.g. display things to the user?
    --
    -- Decryption of encrypted plaintext is equivalent to plaintext.
    -- (encrypted) may not immediately be an ENC, so we need to recurse:
    -- TODO this is not covered by simplifyExpr ? commenting out the part below fails the equivalence3.vp test:
    --
    (CPrimitive p _, CPrimitive p' _) -> equivalencePrimitive p p'
    (CG e, CG e') -> equivalenceExpr e e'
    (a@((:^^:) {}), b@((:^^:) {})) ->
      equivalenceExprs
        (equationToList [] a)
        (equationToList [] b)
    (CItem n e, CItem n' e') -> n == n' && equivalenceExpr e e'
    --
    (CItem {}, _) -> False
    ((:^^:) {}, _) -> False
    (CPrimitive {}, _) -> False
    (CConstant {}, _ ) -> False
    (CG {}, _) -> False

equivalenceExpr :: CanonExpr -> CanonExpr -> Bool
equivalenceExpr e1 e2 = -- TODO cannot be bothered to do transformations both ways
  equivalenceExpr' e1 e2 || equivalenceExpr' e2 e1

equivalenceExprs :: [CanonExpr] -> [CanonExpr] -> Bool
equivalenceExprs [] [] = True
equivalenceExprs (x:xs) (y:ys) = equivalenceExpr x y && equivalenceExprs xs ys
equivalenceExprs _ _ = False

equivalencePrimitive :: PrimitiveP CanonExpr -> PrimitiveP CanonExpr -> Bool
equivalencePrimitive p1 p2 = do
  let eqExpr e1 e2 = equivalenceExpr e1 e2
  let eqExprs [] [] = True
      eqExprs (x:xs) (y:ys) = eqExpr x y && eqExprs xs ys
      eqExprs [] (_:_) = False
      eqExprs (_:_) [] = False
  case (p1, p2) of
    -- TODO is this the right place for this optimization?
    -- NOTE: we do not have any when-guards in here; this way we can
    -- ensure we always progress (by stripping a constructor) and don't
    -- end up in endless loops.
    -- we can however do simple transformations as long as we remove
    -- constructors:
    --(CONCAT e, SPLIT (CPrimitive (CONCAT e') _TODO)) -> eqExprs e e'
    --(SPLIT (CPrimitive (CONCAT e') _TODO), CONCAT e) -> eqExprs e e'
    -- simple equivalence: equivalent constructors, need to
    -- compare the leaf exprs:
    (ASSERT e1 e2, ASSERT e'1 e'2) ->
      eqExpr e1 e'1 && eqExpr e2 e'2
    (ASSERT {}, _) -> False
    (CONCAT e1, CONCAT e'1) -> eqExprs e1 e'1
    (CONCAT {}, _) -> False
    (SPLIT e, SPLIT e') -> eqExpr e e'
    (SPLIT {}, _) -> False
    (HASH e, HASH e') -> eqExprs e e'
    (HASH {}, _) -> False
    (MAC e1 e2, MAC e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (MAC {}, _) -> False
    (HKDF e1 e2 e3, HKDF e'1 e'2 e'3) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3
    (HKDF {}, _) -> False
    (PW_HASH e, PW_HASH e') -> eqExprs e e'
    (PW_HASH {}, _) -> False
    (ENC e1 e2, ENC e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (ENC {}, _) -> False
    (DEC e1 e2, DEC e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (DEC {}, _) -> False
    (AEAD_ENC e1 e2 e3, AEAD_ENC e'1 e'2 e'3) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3
    (AEAD_ENC {}, _) -> False
    (AEAD_DEC e1 e2 e3, AEAD_DEC e'1 e'2 e'3) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3
    (AEAD_DEC {}, _) -> False
    (PKE_ENC e1 e2, PKE_ENC e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (PKE_ENC {}, _) -> False
    (PKE_DEC e1 e2, PKE_DEC e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (PKE_DEC {}, _) -> False
    (SIGN e1 e2, SIGN e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (SIGN {}, _) -> False
    (SIGNVERIF e1 e2 e3, SIGNVERIF e'1 e'2 e'3) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3
    (SIGNVERIF {}, _) -> False
    (RINGSIGN e1 e2 e3 e4, RINGSIGN e'1 e'2 e'3 e'4) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3 && eqExpr e4 e'4
    (RINGSIGN {}, _) -> False
    (RINGSIGNVERIF e1 e2 e3 e4 e5, RINGSIGNVERIF e'1 e'2 e'3 e'4 e'5) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3 && eqExpr e4 e'4 && eqExpr e5 e'5
    (RINGSIGNVERIF {}, _) -> False
    (BLIND e1 e2, BLIND e'1 e'2) -> eqExpr e1 e'1 && eqExpr e2 e'2
    (BLIND {}, _) -> False
    (UNBLIND e1 e2 e3, UNBLIND e'1 e'2 e'3) ->
      eqExpr e1 e'1 && eqExpr e2 e'2 && eqExpr e3 e'3
    (UNBLIND {}, _) -> False
    (SHAMIR_SPLIT e, SHAMIR_SPLIT e') -> eqExpr e e'
    (SHAMIR_SPLIT {}, _) -> False
    (SHAMIR_JOIN e1 e2, SHAMIR_JOIN e'1 e'2) ->
      -- argument order is irrelevant here:
      let a = quicksort [ e1,  e2]
          b = quicksort [e'1, e'2]
      in
        eqExprs a b
    (SHAMIR_JOIN {}, _) -> False

canonicalizePrimitive :: Map Constant Knowledge -> Primitive -> PrimitiveP CanonExpr
canonicalizePrimitive m old =
  mapPrimitiveP old (canonicalizeExpr m)

data CanonExpr
  = CG CanonExpr
  | (:^^:) CanonExpr CanonExpr
  | CConstant Constant CanonKnowledge
  | CPrimitive (PrimitiveP CanonExpr) CheckedPrimitive
  | CItem Int CanonExpr
  deriving (Eq, Ord, Show)
data CanonKnowledge
  = CPrivate
  | CPublic
  | CGenerates
  | CPassword
  deriving (Eq, Ord, Show)
canonicalizeExpr :: Map Constant Knowledge -> Expr -> CanonExpr
canonicalizeExpr m orig_exp = do
  let self = canonicalizeExpr m
  case orig_exp of
    -- TODO we need special handling of G^y^x to G^x^y (sorted in order to check equivalence)
    G exp -> CG (self exp)
    (:^:) const exp -> (:^^:) (self (EConstant const)) (self exp)
    EItem index exp -> CItem index (self exp)
    EConstant const ->
      case Map.lookup const m of
        Just Private -> CConstant const CPrivate
        Just Public -> CConstant const CPublic
        Just Generates -> CConstant const CGenerates
        Just Password -> CConstant const CPassword
        Just (Assignment exp) -> self exp
        Just (Received _) -> CConstant const CPublic -- TODO should never happen
        Just Leaks -> CConstant const CPublic -- TODO should never happen
        Nothing -> CConstant const CPublic -- TODO should never happen
    EPrimitive p cp -> CPrimitive (mapPrimitiveP p self) cp

-- produces an Expr that is still in its canonicalized form,
-- ie we do not refold constant indirections
decanonicalizeExpr :: [(Constant,Knowledge)] -> CanonExpr -> ([(Constant, Knowledge)], Expr)
decanonicalizeExpr m orig_exp = do
  case orig_exp of
    CG exp ->
      do
        let (m1, exp2) = decanonicalizeExpr m exp
        (m1, G exp2)
    (:^^:) oldconst exp -> do
      -- const is an expression which needs to be made into a constant here
      let (m1,rhs) = decanonicalizeExpr m exp
      let (m2,lhs) = decanonicalizeExpr m1 oldconst
          const = Constant {constantName = "aTODO"}
      (((const,Assignment lhs):m2), (:^:) const rhs)
    CConstant const cknow ->
      let eknow = case cknow of
                    CPrivate -> Private
                    CPublic -> Public
                    CGenerates -> Generates
                    CPassword -> Password
      in
        (((const,eknow):m), EConstant const)
    CPrimitive p cp -> do
      let (m2, prim) = mapAccPrimitiveP m p (\m' pr -> decanonicalizeExpr m' pr)
      (m2, EPrimitive prim cp)
    --  CConstant const knowledge -> TODO have to put this in the knowledge map

mapAccPrimitiveP :: aux -> PrimitiveP a -> (aux -> a -> (aux,b)) -> (aux, PrimitiveP b)
mapAccPrimitiveP aux prim f = do
  let nary constr exps = do
        let (aux2,args) = foldl (
              \(aux,acc) exp ->
                let (aux',m1) = f aux exp in (aux',m1:acc)
              ) (aux,[]) exps
        (aux2, constr (Prelude.reverse args))
      arity1 constr e1 =
        let (aux1, m1) = f aux e1
        in (aux1, constr m1)
      arity2 constr e1 e2 =
        let (aux1, constr') = arity1 constr e1
            (aux2, m2) = f aux1 e2
        in (aux2, constr' m2)
      arity3 constr e1 e2 e3 =
        let (aux2, constr') = arity2 constr e1 e2
            (aux3, m3) = f aux2 e3
        in (aux3, constr' m3)
      arity4 constr e1 e2 e3 e4 =
        let (aux3, constr') = arity3 constr e1 e2 e3
            (aux4, m4) = f aux3 e4
        in (aux4, constr' m4)
      arity5 constr e1 e2 e3 e4 e5 =
        let (aux4, constr') = arity4 constr e1 e2 e3 e4
            (aux5, m5) = f aux4 e5
        in (aux5, constr' m5)
  case prim of
    ASSERT e1 e2 -> arity2 ASSERT e1 e2
    CONCAT exps -> nary CONCAT exps
    SPLIT e1 -> arity1 SPLIT e1
    HASH exps -> nary HASH exps
    MAC e1 e2 -> arity2 MAC e1 e2
    HKDF e1 e2 e3 -> arity3 HKDF e1 e2 e3
    PW_HASH exps -> nary PW_HASH exps
    ENC e1 e2 -> arity2 ENC e1 e2
    DEC e1 e2 -> arity2 DEC e1 e2
    AEAD_ENC e1 e2 e3 -> arity3 AEAD_ENC e1 e2 e3
    AEAD_DEC e1 e2 e3 -> arity3 AEAD_DEC e1 e2 e3
    PKE_ENC e1 e2 -> arity2 PKE_ENC e1 e2
    PKE_DEC e1 e2 -> arity2 PKE_DEC e1 e2
    SIGN e1 e2 -> arity2 SIGN e1 e2
    SIGNVERIF e1 e2 e3 -> arity3 SIGNVERIF e1 e2 e3
    RINGSIGN e1 e2 e3 e4 -> arity4 RINGSIGN e1 e2 e3 e4
    RINGSIGNVERIF e1 e2 e3 e4 e5 -> arity5 RINGSIGNVERIF e1 e2 e3 e4 e5
    BLIND e1 e2 -> arity2 BLIND e1 e2
    UNBLIND e1 e2 e3 -> arity3 UNBLIND e1 e2 e3
    SHAMIR_SPLIT e1 -> arity1 SHAMIR_SPLIT e1
    SHAMIR_JOIN e1 e2 ->
      let (aux1, m1) = f aux e1
          (aux2, m2) = f aux1 e2
      in (aux2, SHAMIR_JOIN m1 m2)

mapPrimitiveP :: PrimitiveP a -> (a -> b) -> PrimitiveP b
mapPrimitiveP prim f = snd (mapAccPrimitiveP () prim (\() a -> ((), f a)))

-- note that this ONLY folds over the constants in an expression,
-- NOT the knowledge maps, so it will not "jump" across maps of knowledge
-- from other principals.
foldConstantsInExpr :: acc -> Expr -> (Constant -> acc -> acc) -> acc
foldConstantsInExpr acc o_exp f =
  let dolist = foldl (\acc exp -> foldConstantsInExpr acc exp f) acc in
  case o_exp of
    EItem _TODOFIXME exp -> dolist [exp]
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
        SHAMIR_JOIN e1 e2 -> dolist [e1, e2]

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
    Nothing -> addError (MissingConstant const)
