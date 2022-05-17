{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace()

import Data.Graph.Inductive.Graph() -- (mkGraph, LNode, LEdge, OrdGr, DynGraph(..), empty, Graph, gfiltermap)
import Data.Graph.Inductive.Basic() -- (elfilter)
import Data.Graph.Inductive.NodeMap() --fromGraph)--,NodeMap(..))
import Data.Graph.Inductive.Query.SP

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
  , msConfidentialityGraph :: OrdGr Gr CanonExpr (Set (Set CanonExpr))
  } deriving (Eq, Ord, Show)

type ProcessingCounter = Int

data PT = PT (Int,(Set (Set CanonExpr))) deriving (Show,Eq,Ord)
instance Real PT where
  toRational (PT (t,_s)) = toRational (toInteger t)
instance Num PT where
    (PT (x,s)) + (PT (y,_s')) = PT (x + y, s)
    --(PT (x,s)) - (PT (y,s')) = PT (x + y, Set.union s s')
    negate (PT (x,s)) = PT (negate x, s)
    (PT (x,_)) * (PT (y,s)) = PT (x*y,s) -- TODO
    abs (PT (x,s)) = PT (abs x, s)
    signum a = a
    fromInteger t = PT (fromInteger t, Set.empty)

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
  , msConfidentialityGraph = OrdGr (mkGraph [] [])
  }

type EvalM a = State ModelState a

upsertMapNodeM :: CanonExpr -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
upsertMapNodeM v = do
  (nm, g) <- get
  let (node, _v) = mkNode_ nm v
  case gelem node g of
    False -> do
      _ <- insMapNodeM v
      pure ()
    True -> pure ()

-- https://hackage.haskell.org/package/containers-0.6.5.1/docs/Data-Set.html
--
--  Nodes: CanonExpr
--    -- unlocked by: Set of Set of CanonExpr
--  Or   Set CanonExpr -/      |
--  And  Set CanonExpr --------/
--
-- Foreach principal we make a CanonExpr Constant PrincipalName"_Knows"
--   and then filter the edges
--      removing Set elements not known to principal
--        equivalentExpr in principalKnowledge
--      removing edges where the set is empty
--   once edges are removed, the remaining paths should lead to expressions
--   that can be reached by the principal, so foreach of those
--     add edge directly from principal to this
--   repeat if number of nodes is different from loop beginning
buildKnowledgeGraph :: ModelState -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
buildKnowledgeGraph ms = do
  --let -- compute transitive reflexive closure aka compute reachability for each vertice pair:
  --gtrc = Data.Graph.Inductive.Query.TransClos.trc g
  -- shortest path: Data.Graph.Inductive.Query.SP
  let nil = CConstant (Constant "nil") CPublic
      attacker = CConstant (Constant "attacker") CPrivate
  upsertMapNodeM nil
  upsertMapNodeM attacker
  let edge_always = Set.singleton $ Set.empty -- 'OR(AND())' always matches
      constmap = msConstants ms
      foldCanonExpr :: CanonExpr -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr CanonExpr
      foldCanonExpr c_expr = do
        upsertMapNodeM c_expr
        let simpl = simplifyExpr c_expr
        unless (simpl == c_expr) $ do
          upsertMapNodeM simpl
          -- learn simpl by knowing c_expr
          insMapEdgeM (c_expr,simpl, edge_always)
        case c_expr of
          CPrimitive (ENC key msg) _ -> do
            upsertMapNodeM key
            upsertMapNodeM msg
            _ <- foldCanonExpr key
            _ <- foldCanonExpr msg
            -- learn msg by knowing ENC(key,msg) & key
            insMapEdgeM (c_expr,msg,(Set.singleton $ Set.fromList [c_expr,key]))
            -- learn c_expr by knowing key & msg
            insMapEdgeM (key,c_expr,(Set.singleton $ Set.fromList [msg]))
            pure simpl
          CPrimitive (DEC key ciphertext) _ -> do
            -- attacker can DEC() if they know key & ciphertext:
            insMapEdgeM (key, simpl, Set.singleton $ Set.singleton ciphertext)
            -- attacker can ENC() if they know key & simpl:
            insMapEdgeM (simpl, ciphertext, Set.singleton $ Set.singleton key)
            pure simpl
          CPrimitive (AEAD_ENC key plaintext ad) _ -> do
            -- attacker can compute AEAD_ENC() if they know all the args:
            insMapEdgeM (key, simpl, Set.singleton $ Set.fromList [plaintext, ad])
            insMapEdgeM (ad, simpl, Set.singleton $ Set.fromList [plaintext, key])
            insMapEdgeM (plaintext, simpl, Set.singleton $ Set.fromList [key, ad])
            -- attacker can decrypt if they know key and ad:
            -- TODO can attackers decrypt it without knowing AD? this seems
            -- TODO worth documenting as it might not correspond to how people
            -- TODO define AEADs? (ie is the key derived from HASH(ad), or is ad
            -- TODO only relevant for verifying the mac?)
            insMapEdgeM (simpl, plaintext, Set.singleton $ Set.fromList [key, ad])
            pure simpl
          CPrimitive (AEAD_DEC key ciphertext ad) _ -> do
            -- attacker can decrypt if they know args:
            insMapEdgeM (key, simpl, Set.singleton $ Set.fromList [ciphertext,ad])
            insMapEdgeM (ciphertext, simpl, Set.singleton $ Set.fromList [key,ad])
            insMapEdgeM (ad, simpl, Set.singleton $ Set.fromList [key,ciphertext])
            -- attacker can re-encrypt:
            insMapEdgeM (simpl, ciphertext, Set.singleton $ Set.fromList [key,ad])
            pure simpl
          CPrimitive (CONCAT lst) _ -> do
            foo <- foldM (\acc exp -> do
                             x <- foldCanonExpr exp
                             -- knowing CONCAT(x,..) leads to knowing x,..
                             insMapEdgeM (simpl,x, edge_always)
                             pure (x:acc)
                         ) [] lst
            case foo of
              x:xs -> do
                -- knowing x leads to simple if you also know xs
                _ <- insMapEdgeM (x,simpl, Set.singleton $ (Set.fromList xs))
                pure simpl
              [] -> do
                _ <- insMapEdgeM (nil,simpl, edge_always)
                pure simpl
          CPrimitive (HASH lst) _ -> do
            foo <- foldM (\acc exp -> do
                             x <- foldCanonExpr exp
                             pure (x:acc)
                         ) [] lst
            case foo of
              x:xs -> do
                -- knowing x leads to simple if you also know xs
                _ <- insMapEdgeM (x,simpl, Set.singleton $ (Set.fromList xs))
                pure simpl
              [] -> do
                _ <- insMapEdgeM (nil,simpl, edge_always)
                pure simpl
          CItem n (CPrimitive (SPLIT (CPrimitive (CONCAT lst) _)) _) -> do
            case Data.List.drop n lst of
              item:_ -> do
                insMapEdgeM (simpl,item,edge_always)
                insMapEdgeM (item,simpl,edge_always)
                pure simpl
              [] -> pure simpl
          CItem _ _ -> do
            pure simpl -- TODO
          CConstant _ CPublic -> do
            -- attacker knows this because it's public
            insMapEdgeM (attacker, simpl, edge_always)
            pure simpl
          CConstant _ _ -> do
            pure simpl -- the attacker knows nothing, john snow
          CG secret -> do
            -- attacker can always lift to the power of G
            insMapEdgeM (secret, simpl, edge_always)
            pure simpl
          (:^^:) lhs rhs -> do
            -- attacker can calculate powers
            insMapEdgeM (lhs, simpl, Set.singleton $ Set.singleton rhs)
            insMapEdgeM (rhs, simpl, Set.singleton $ Set.singleton lhs)
            -- TODO knowing G^a^b leads to knowing G^b^a:
            -- TODO is this really wonky?
            case simplifyExpr lhs of
              CG lhs_s -> do
                let switched = (:^^:) (CG rhs) lhs_s
                upsertMapNodeM switched
                insMapEdgeM (switched, simpl, edge_always)
                insMapEdgeM (simpl, switched, edge_always)
                pure simpl
              _ -> pure simpl
          CPrimitive (ASSERT _ _) _ -> do
            -- TODO this is kind of a special case in that ASSERT() can reference
            -- variables unknown to the principal. It should not be allowed to
            -- capture the output of ASSERT() ???
            pure simpl
          CPrimitive (SPLIT exp) _ -> do
            -- TODO technically it should only lead to knowing the first element
            -- if SPLIT() is contained within another expression
            -- simple leads to exp:
            case simplifyExpr exp of
              CPrimitive (CONCAT (first:_)) _ -> do
                insMapEdgeM (simpl, first, edge_always)
                pure ()
              _ -> pure ()
            -- attacker can always compute exp -> SPLIT(exp)
            insMapEdgeM (exp, simpl, edge_always)
            pure simpl
          CPrimitive (MAC key msg) _ -> do
            -- MAC produces a hash, so neither key/msg are leaked,
            -- but the attacker does get to reconstruct it if they know
            -- the key and the msg:
            insMapEdgeM (key, simpl, Set.singleton $ Set.singleton msg)
            pure simpl
          CPrimitive (HKDF salt ikm info) _ -> do
            -- attacker can reconstruct this by knowing the args:
            insMapEdgeM (salt, simpl, Set.singleton $ Set.fromList [ikm, info])
            pure simpl
          CPrimitive (PW_HASH []) _ -> do
            -- everyone can compute this:
            insMapEdgeM (nil, simpl, edge_always)
            pure simpl
          CPrimitive (PW_HASH (x:xs)) _ -> do
            -- attacker can compute PW_HASH if it knows the args:
            insMapEdgeM (x, simpl, Set.singleton $ Set.fromList xs)
            pure simpl
          CPrimitive (SIGN key message) _ -> do
            -- attacker can reconstruct from args:
            insMapEdgeM (key,simpl,Set.singleton $ Set.singleton message)
            insMapEdgeM (message,simpl,Set.singleton $ Set.singleton key)
            pure simpl
          CPrimitive (SIGNVERIF _pk@(CG secret) message _signed@(CPrimitive (SIGN secret' message') _)) _
            | equivalenceExpr secret secret' && equivalenceExpr message message' -> do
                -- anyone who knows verified message knows the message:
                insMapEdgeM (simpl, message, edge_always)
                -- TODO there's more stuff to learn for the attacker here
                pure simpl
          CPrimitive (SIGNVERIF {}) _ -> pure simpl
          CPrimitive (RINGSIGN {}) _ -> do
            -- TODO this one is fun, but complicated. TODO
            pure simpl
          CPrimitive (RINGSIGNVERIF {}) _ -> do
            pure simpl -- TODO
          CPrimitive (BLIND {} ) _ -> pure simpl -- TODO
          CPrimitive (UNBLIND {}) _ -> pure simpl -- TODO
          CPrimitive (SHAMIR_SPLIT {} ) _ -> pure simpl -- TODO
          CPrimitive (SHAMIR_JOIN {}) _ -> pure simpl -- TODO
          CPrimitive (PKE_ENC pk plaintext) _ -> do
            insMapEdgeM (plaintext, simpl, Set.singleton $ Set.singleton pk)
            insMapEdgeM (pk, simpl, Set.singleton $ Set.singleton plaintext)
            case simplifyExpr pk of
              CG secret -> do
                -- attacker can decrypt if the know secret and simpl:
                insMapEdgeM (secret, plaintext, Set.singleton $ Set.singleton simpl)
                pure simpl
              _ -> pure simpl -- TODO this should be a type error?
          CPrimitive (PKE_DEC key ciphertext) _ -> do
            -- reconstruct from args:
            insMapEdgeM (key, simpl, Set.singleton $ Set.singleton ciphertext)
            insMapEdgeM (ciphertext, simpl, Set.singleton $ Set.singleton key)
            -- re-encrypt:
            insMapEdgeM (simpl, ciphertext, Set.singleton $ Set.singleton key)
            pure simpl
          --unhandledTODO -> do -- TODO only here to help detect unhandled cases
          --  Debug.Trace.traceShow unhandledTODO $ pure simpl
          -- case False of
          --    True -> pure () -- can never happen, this is a crash assertion
          --  pure simpl -- TODO remove this
  foldM (\st (const,_knowledge) -> do
            --insMapNodeM (knowledge)
            let c_expr = canonicalizeExpr constmap (EConstant const)
            _ <- foldCanonExpr c_expr
            --  CConstant c2 _knowl -> insMapNodeM c2
            --  CPrimitive (ENC key msg) _ ->
            --   foldConstantsInExpr
            --  _ -> insMapNodeM const
            --case knowledge of
            --  Ass
            --insMapEdgeM (const,const,c_expr)
            pure st
        ) () (Map.assocs constmap)
  foldM (\() (principalName, principalMap) -> do
            let cprName = CConstant (Constant principalName) CPrivate
            upsertMapNodeM cprName
            foldM (\() (c,(knowledge,_counter)) -> do
                      let c_expr = canonicalizeExpr constmap (EConstant c)
                      --insMapNodeM c_expr
                      insMapEdgeM (cprName,c_expr,edge_always)
                      case knowledge of
                        Leaks -> do
                          -- attacker learns it because it's leaked:
                          insMapEdgeM (attacker, c_expr,edge_always)
                          pure ()
                        Received _ -> do
                          -- attacker learns it from the wire:
                          insMapEdgeM (attacker, c_expr,edge_always)
                          pure ()
                        _ -> pure ()
                  ) () $ Map.assocs principalMap
            pure () ) () $ Map.assocs $ msPrincipalConstants ms

process :: Model -> ModelState
process model =
  execState (processM model) emptyModelState

processM :: Model -> State ModelState ()
processM Model{..} = do
  mapM_ processModelPart modelParts

processModelPart :: ModelPart -> State ModelState ()
processModelPart (ModelPrincipal (Principal name knows)) = do
  mapM_ (processKnowledge name) knows
processModelPart (ModelQueries qs) = do
  -- ModelQueries should be the last ModelPart, so we should be safe to compute
  -- the graph of what the attacker can reach:
  errors <- gets msErrors
  unless ((/=) errors ([]::[ModelError])) $ do
    modify $ \state -> do
      let (_nodemap,gr) = execState (buildKnowledgeGraph state) (new,mkGraph [] [])
      state { msConfidentialityGraph = OrdGr gr }
    mapM_ processQuery qs
  -- TODO if the user wrote the same query twice
  -- we should collapse them to a single query
  -- and probably issue a warning?
  

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

processModelPart (ModelPhase (Phase {})) = do
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
    \() constant ->
      if constantName constant == "_"
      then pure ()
      else do
        existingConstant <- getConstant constant
        case existingConstant of
          Nothing ->
            if knowledge == Leaks
            then addError (MissingConstant constant)
            else pure ()
          Just _e_k ->
            if canOverlap knowledge
            then pure()
            else addError (OverlappingConstant constant)
    ) () constants
  let addThem () = foldM_ (
        \() constant -> do
          existingConstant <- getConstant constant
          case (existingConstant, knowledge, canOverlap knowledge) of
            (Nothing, Leaks, _) ->
              addError (MissingConstant constant)
            (Nothing, _, _) | knowledge /= Leaks -> addConstant principalName constant knowledge
            -- principal A [ knows public x ] principal B [ knows public X ]
            (Just existing, Leaks, _) ->
              upsertPrincipalConstant "attacker" constant existing
            (Just oldknowledge, _, True)
              | oldknowledge == knowledge ->
                upsertPrincipalConstant principalName constant knowledge
            (Just _, _, _) -> addError (OverlappingConstant constant)
        ) () constants
  case knowledge of
    Assignment (EConstant rhs) -> addError $ ValueToValue (Data.List.NonEmpty.head constants) rhs
    Assignment exp -> processAssignment principalName constants exp
    Public -> addThem ()
    Private -> addThem ()
    Password -> addThem ()
    Generates -> addThem ()
    Leaks -> addThem ()
    Received _ -> addThem ()

processQuery :: Query -> State ModelState ()
processQuery query@(Query (FreshnessQuery constant) _TODO_queryOptions) = do
  constantExistsOrError constant
  cs <- gets msConstants ;
  addQueryResult query $ mapConstants False constant (
    \c a -> a || Just Generates == Map.lookup c cs) cs

processQuery query@(Query (ConfidentialityQuery constant) _TODO_queryOptions) = do
  constantExistsOrError constant
  g <- gets msConfidentialityGraph
  --let g' = elfilter (\ssc -> True) (unOrdGr g)
  pure ()
  let _trc = Data.Graph.Inductive.Query.TransClos.trc (unOrdGr g)
  -- nm = Data.Graph.Inductive.NodeMap.fromGraph (unOrdGr g)
  constmap <- gets msConstants
  let mf :: Context CanonExpr (Set (Set CanonExpr)) -> MContext CanonExpr PT
      mf = (\(b_in,a,c,b_out) -> do
               -- Debug.Trace.traceShow foo $ pure ()
               let b_in' :: Adj PT
                   b_in' = Data.List.map (\(s,n) -> (PT (1,s),n)) b_in
                   b_out' :: Adj PT
                   b_out' = Data.List.map (\(s,n) -> (PT (1,s),n)) b_out
                   ret :: MContext CanonExpr PT
                   ret = Just (b_in',a,c,b_out')
               ret
           )
      rg :: Gr CanonExpr PT
      rg = gfiltermap mf (unOrdGr g)
  --let rg = emap (\w -> 1) trc
  -- Basic.elfilter
  let attackerL = labfilter ((==) (CConstant (Constant "attacker") CPrivate)) (unOrdGr g)
      attacker = case nodes attackerL of
        [n] -> n
        _ -> 1 -- TODO this should never be reached
  case Data.Graph.Inductive.Query.SP.spTree attacker rg of
    [] -> addQueryResult query True
    paths -> do
      let attackerSetOrigin = Set.empty
          foldPaths :: Set CanonExpr -> Set CanonExpr
          foldPaths aso = foldl inner2 (aso) (Data.List.reverse paths)
          inner1 :: (Bool, Set CanonExpr) -> (Node, PT) -> (Bool, Set CanonExpr)
          inner1 (sofar, thisSet) (node, PT (_, preconditions)) = do
            if not sofar
              then (sofar,thisSet)
              else do
              let canGet = foldl (\acc required -> acc || null (Set.difference required thisSet) || foldl (\acc ce -> acc && foldl (\acc2 ae -> acc2 || equivalenceExpr ce ae) False thisSet) True required ) False preconditions
                  c_expr = case lab (unOrdGr g) $ node of
                             Just e -> e
              if canGet
                then do
                --let res :: (Bool, Set CanonExpr)
                --    res = pure (True, Set.insert (simplifyExpr c_expr) $ (Set.insert c_expr) thisSet)
                let res = (Set.insert (simplifyExpr c_expr) $ (Set.insert c_expr thisSet))
                if Set.member c_expr thisSet
                  then (True, res) -- already know this
                  else do
                  let res2 = res --Debug.Trace.traceShow (c_expr) $ res
                  (True, res2) --Debug.Trace.traceShow (c_expr) $ res
                else (False, thisSet) -- attacker can't reach this
          inner2 :: Set CanonExpr -> LPath PT -> Set CanonExpr
          inner2 attackerSet path = snd (foldl inner1 (True,attackerSet) (unLPath path)) -- (Data.List.reverse ))
          news = foldPaths attackerSetOrigin
      let canon_constant :: CanonExpr
          canon_constant = simplifyExpr $ canonicalizeExpr constmap (EConstant (constant))
          todo_news :: Set CanonExpr
          todo_news = while_new news
          while_new :: Set CanonExpr -> Set CanonExpr
          while_new old =
            let newer = foldPaths old in
            if old == newer
            then old
            else while_new newer
      --_ <- Debug.Trace.traceShow todo_news $ pure ()
      let attacker_knows = foldl (\knows cexpr -> knows || equivalenceExpr cexpr canon_constant) False todo_news
      addQueryResult query (not attacker_knows)
  pure ()

processQuery (Query (UnlinkabilityQuery consts) _TODO_queryOptions) = do
  forM_ consts $ \cconst -> constantExistsOrError cconst
  addError (NotImplemented "unlinkability query not implemented") -- FIXME

processQuery (Query (AuthenticationQuery _msg) _TODO_queryOptions) = do
  addError (NotImplemented "authentication query not implemented") -- FIXME

processQuery (Query (EquivalenceQuery []) _queryOptions) = pure ()

processQuery query@(Query (EquivalenceQuery consts@(c1:_)) _TODO_queryOptions) = do
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
  Received _ -> True -- TODO

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
hasPrincipalConstantOrError principalName refconstant _errorText = do
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
equivalenceExpr e1 e2 =
  equivalenceExpr' e1 e2

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
  deriving (Eq, Ord, Show, Enum)
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
    CItem idx cp -> do
      let (m1,rhs) = (decanonicalizeExpr m cp)
      (m1, (EItem idx rhs))
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
    EItem _TODOFIXME exp -> dolist [exp] -- TODO we need testcases that hit this path
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
