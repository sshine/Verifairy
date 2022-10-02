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
import Debug.Trace(traceShow)
import Data.Tree
import Text.Show.Pretty (ppDoc)

import Data.Graph.Inductive.Graph() -- (mkGraph, LNode, LEdge, OrdGr, DynGraph(..), empty, Graph, gfiltermap)
import Data.Graph.Inductive.Basic() -- (elfilter)
import Data.Graph.Inductive.NodeMap() --fromGraph)--,NodeMap(..))
--import Data.Graph.Inductive.Query.SP

--import Data.Graph.Inductive.PatriciaTree
--import Data.Graph.Inductive.Query.TransClos
import qualified Data.Graph.Inductive.Query.DFS

data ModelError
  = OverlappingConstant Constant
  | MissingConstant Constant
  | ValueToValue Constant Constant
  | NotImplemented Text
  | AssertionFailed CanonExpr CanonExpr
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
  , msPhases             :: [(Phase, ProcessingCounter)] -- ^-- all constants known by Phase will have their counter <  ProcessingCounter
  , msQueryResults       :: [(Query, Bool)]
  -- need OrdGr in order to derive Ord for ModelState:
  , msConfidentialityGraph :: OrdGr Gr CanonExpr (Set (Set CanonExpr))
  , msPrincipalConfidentialityGraph :: Map PrincipalName (OrdGr Gr CanonExpr (Set (Set CanonExpr))) -- ^-- all the values each principal can reach
  , msPrincipalConfidentialitySet :: Map PrincipalName (Set CanonExpr) -- ^-- a set of the nodes in principal's msPrincipalConfidentialityGraph
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
  , msPhases = []
  , msQueryResults = []
  , msConfidentialityGraph = OrdGr (mkGraph [] [])
  , msPrincipalConfidentialityGraph = Map.empty
  , msPrincipalConfidentialitySet = Map.empty
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

upsertEdgeM :: (CanonExpr, CanonExpr, Set (Set CanonExpr)) -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
upsertEdgeM edge@(a,b,ssc) = do
  -- FIXME we currently have a problem in that HasQuestionMark / HasntQuestionMark
  -- causes trivial comparison with == to fail, so perhaps we should
  -- insert both here? or get rid of it from CanonExpr ?
  (nm, g) <- get
  let (a_node, _) = mkNode_ nm a -- get the numeric Node corresponding to label a
      (b_node, _) = mkNode_ nm b
      incoming :: [LEdge (Set (Set CanonExpr))]
      incoming = inn g b_node -- Find all inward-bound LEdges for the given Node.
  updated <- foldM (\acc (xa,_b,xssc) ->
                      if acc || xa /= a_node
                      then pure acc
                      else do
                        delMapEdgeM (a,b)
                        insMapEdgeM (a,b,Set.union xssc ssc)
                        pure True
                   ) False incoming
  if updated then pure () else do
    insMapEdgeM edge
    pure ()

addPasswordBruteforceEdges :: NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
addPasswordBruteforceEdges = do
  -- by 3.2) we let the attacker bruteforce passwords if they do not
  -- come from a PW_HASH() function
  (_nm, g) <- get
  let pw_g = labfilter (
        \n -> case n of
          CConstant _ CPassword -> True
          _ -> False
        ) g
      pw_nodes = nodes pw_g
      f :: Context CanonExpr (Set (Set CanonExpr)) -> (CanonExpr,Node,Adj (Set (Set CanonExpr)),Bool)
      f (adj_in, node, label, adj_out) =
        case simplifyExpr label of
          CPrimitive (PW_HASH _) _ -> (label,node,[], True)
          _ -> (label, node,adj_in, False)
      forest :: Data.Tree.Forest (CanonExpr,Node,Adj (Set (Set CanonExpr)),Bool)
      forest = dffWith f (Data.List.reverse pw_nodes) g
      -- TODO why is forest /== forests ?
      -- would be nice to have a property test that detects when we use
      -- "forest" instead of "forests" here; see confidentiality30.vp
      forests = (Data.List.map (\node -> dffWith f [node] g ) pw_nodes)
      --foldTree :: (a -> [b] -> b) -> Tree a -> b
      recurse :: CanonExpr -> Tree (CanonExpr,Node,Adj (Set (Set CanonExpr)),Bool) -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
      recurse pw tree =
        let (top, top_node, top_edges_in, is_pwhash) = rootLabel tree in
          if is_pwhash
          then pure ()
          else do
            foldM (\() subtree -> do
                      (_, g) <- get
                      let (sub_label, sub_node, _edges, next_ispwh) = rootLabel subtree
                          outgoing = lsuc g sub_node
                      mapM_ (\(edge_node,old_preconds) ->
                               if not next_ispwh
                               then
                                 case lab g edge_node of
                                   Just receiver -> upsertEdgeM (sub_label,top,Set.map (Set.filter (\req -> req /= top && req /= sub_label && req /= pw)) old_preconds)
                               else pure ()
                            ) outgoing
                      recurse pw subtree
                  ) () (subForest tree)
      analyzeAllTheForests = do
        -- foldM (\() x -> asd x) () forest
        foldM (\() forest -> do
                  foldM_ (\() forest ->
                            let (pw,_,_,_) = rootLabel forest in
                              recurse pw forest
                         ) () forest
              ) () forests
      -- Data.Tree.drawForest
  analyzeAllTheForests
  (_nm, g') <- get
  if g /= g' -- run until results have settled:
    then addPasswordBruteforceEdges
    else pure ()
  -- dffWith :: Graph gr => CFun a b c -> [Node] -> gr a b -> [Tree c]
  -- dffWith f pw_nodes g
  -- xdfWith :: Graph gr => CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> ([Tree c], gr a b)
  -- (tree, newg) = xdfWith suc' f pw_nodes g
  -- forall CPassword
  --   do BFS
  --     if node is PW_HASH:
  --       stop
  --     upsertEdgeM (node, parent, Set.singleton $ Set.singleton bruteforce)

upsertEdgePermutationsM :: [CanonExpr] -> CanonExpr -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr ()
upsertEdgePermutationsM args lead_to = do
  let arg_set = Set.fromList args
  foldM (\() x -> do
            let diffset = Set.difference arg_set (Set.singleton x)
            upsertEdgeM (x, lead_to, Set.singleton $ diffset)
            upsertEdgeM (lead_to, x, Set.singleton $ arg_set)
        ) () args

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
      leaks = CConstant (Constant "leaks") CPrivate
      public = CConstant (Constant "public") CPrivate
      sent = CConstant (Constant "sent") CPrivate
      attacker = CConstant (Constant "attacker") CPrivate
      edge_always = Set.singleton $ Set.empty -- 'OR(AND())' always matches
  upsertMapNodeM nil
  upsertMapNodeM leaks
  upsertMapNodeM public
  upsertMapNodeM sent
  upsertMapNodeM attacker
  upsertEdgeM (attacker,leaks,edge_always)
  upsertEdgeM (attacker,public,edge_always)
  upsertEdgeM (attacker,sent,edge_always)
  --upsertEdgeM (attacker,nil,edge_always)
  let constmap = msConstants ms
      foldCanonExpr :: CanonExpr -> NodeMapM CanonExpr (Set (Set CanonExpr)) Gr CanonExpr
      foldCanonExpr c_expr = do
        upsertMapNodeM c_expr
        let simpl = simplifyExpr c_expr
        unless (simpl == c_expr) $ do
          upsertMapNodeM simpl
          -- learn simpl by knowing c_expr
          upsertEdgeM (c_expr,simpl, edge_always)
          upsertEdgeM (simpl,c_expr, edge_always)
        case c_expr of
          CPrimitive (ENC key msg) _ -> do
            s_key <- foldCanonExpr key
            s_msg <- foldCanonExpr msg
            -- learn msg by knowing ENC(key,msg) & key
            upsertEdgeM (simpl,s_msg,(Set.singleton $ Set.singleton s_key))
            -- reencrypt by knowing key & msg:
            upsertEdgePermutationsM [s_key,s_msg] simpl
            pure simpl
          CPrimitive (DEC key ciphertext) _ -> do
            s_key <- foldCanonExpr key
            s_ciphertext <- foldCanonExpr ciphertext
            -- attacker can DEC() if they know key & ciphertext:
            upsertEdgePermutationsM [s_key,s_ciphertext] simpl
            -- attacker can ENC() if they know key & simpl:
            upsertEdgeM (simpl, s_ciphertext, Set.singleton $ Set.singleton s_key)
            pure simpl
          CPrimitive (AEAD_ENC key plaintext ad) _ -> do
            s_key <- foldCanonExpr key
            s_plaintext <- foldCanonExpr plaintext
            s_ad <- foldCanonExpr ad
            -- attacker can compute AEAD_ENC() if they know all the args:
            upsertEdgePermutationsM [s_key,s_plaintext,s_ad] simpl
            -- attacker can decrypt if they know key and ad:
            -- TODO can attackers decrypt it without knowing AD? this seems
            -- TODO worth documenting as it might not correspond to how people
            -- TODO define AEADs? (ie is the key derived from HASH(ad), or is ad
            -- TODO only relevant for verifying the mac?)
            upsertEdgeM (simpl, s_plaintext, Set.singleton $ Set.fromList [s_key, s_ad])
            pure simpl
          CPrimitive (AEAD_DEC key ciphertext ad) _ -> do
            s_key <- foldCanonExpr key
            s_ciphertext <- foldCanonExpr ciphertext
            s_ad <- foldCanonExpr ad
            -- attacker can decrypt if they know args:
            upsertEdgePermutationsM [s_key,s_ciphertext,s_ad] simpl
            -- attacker can re-encrypt:
            upsertEdgeM (simpl, ciphertext, Set.singleton $ Set.fromList [key,ad])
            pure simpl
          CPrimitive (CONCAT lst) _ -> do
            simple_lst <- foldM (\acc exp -> do
                                     x <- foldCanonExpr exp
                                     pure (x:acc)
                                 ) [] lst
            let simple_set = Set.fromList simple_lst
            -- attacker can reconstruct if they know all the arguments:
            -- knowing x,.. leads to CONCAT(x,..)
            upsertEdgePermutationsM simple_lst simpl
            -- TODO wtf: why does "nil," work here but "attacker," doesn't?
            upsertEdgeM (nil,simpl,Set.singleton $ simple_set)
            () <- foldM (\() x -> do
                           -- knowing CONCAT(x,..) leads to knowing x,..
                           upsertEdgeM (simpl,x, edge_always)
                           pure ()
                       ) () simple_lst
            pure simpl
          CPrimitive (HASH hash_lst) _ -> do
            simple_lst <- foldM (\acc exp -> do
                             x <- foldCanonExpr exp
                             pure (x:acc)
                         ) [] (hash_lst)
            case simple_lst of
              [] -> do
                -- anyone can do this:
                upsertEdgeM (nil,simpl, edge_always)
              _:_ -> do
                upsertEdgePermutationsM simple_lst simpl -- TODO also hash_lst?
            pure simpl
          CItem n wever -> do
            s_wever <- foldCanonExpr wever
            --upsertEdgeM (wever, simpl, edge_always) -- explicitly not the simple version
            let getitem lst = do
                  simple_lst <- foldM (\acc exp -> do
                                          x <- foldCanonExpr exp
                                          pure (x:acc)
                                      ) [] (Data.List.reverse lst)
                  case Data.List.drop n simple_lst of
                    item:_ -> do
                      upsertEdgeM (simpl,item,edge_always)
                      upsertEdgeM (item,simpl,edge_always)
                      pure ()
                    [] -> pure ()
            () <- case wever of
                    (CPrimitive (SPLIT maybeconcat) _) -> do
                      upsertEdgeM (maybeconcat, wever, edge_always)
                      upsertEdgeM (maybeconcat, simpl, edge_always)
                      case maybeconcat of
                        (CPrimitive (CONCAT lst) _) -> do
                          getitem lst
                        _bad -> pure ()
                    (CPrimitive (HKDF a b c) _) -> do
                        upsertEdgeM (wever,simpl,edge_always)
                        -- attacker can confirm knowledge of parameters a,b,c
                        -- if they see a 'simpl' output:
                        upsertEdgeM (simpl,wever, Set.singleton (Set.fromList [a,b,c]))
                    _ -> pure ()
            pure simpl -- TODO
          CConstant _ CPublic -> do
            -- attacker knows this because it's public
            upsertEdgeM (public, simpl, edge_always)
            pure simpl
          CConstant _ _ -> do
            pure simpl -- the attacker knows nothing, john snow
          CG secret -> do
            s_secret <- foldCanonExpr secret
            -- attacker can always lift to the power of G
            upsertEdgeM (s_secret, simpl, edge_always)
            pure simpl
          (:^^:) lhs rhs -> do
            s_lhs <- foldCanonExpr lhs
            s_rhs <- foldCanonExpr rhs
            -- attacker can calculate powers
            upsertEdgePermutationsM [s_lhs, s_rhs] simpl
            -- TODO knowing G^a^b leads to knowing G^b^a:
            -- TODO is this really wonky?
            case s_lhs of
              CG lhs_s -> do
                let rhs_pub = CG s_rhs
                    switched = (:^^:) rhs_pub lhs_s
                upsertMapNodeM rhs_pub
                upsertMapNodeM switched
                upsertEdgeM (switched, simpl, edge_always)
                upsertEdgeM (simpl, switched, edge_always)
                upsertEdgeM (s_rhs, rhs_pub, edge_always)
                -- knowing G^rhs & lhs_secret leads to knowing G^rhs^lhs_secret:
                upsertEdgeM (rhs_pub, switched, Set.singleton $ Set.singleton lhs_s)
                pure simpl
              _ -> pure simpl
          CPrimitive (ASSERT _ _) _ -> do
            -- TODO this is kind of a special case in that ASSERT() can reference
            -- variables unknown to the principal(??) It should not be allowed to
            -- capture the output of ASSERT() ???
            pure simpl
          CPrimitive (SPLIT exp) _ -> do
            s_exp <- foldCanonExpr exp
            -- attacker can always compute exp -> SPLIT(exp)
            upsertEdgeM (exp, simpl, edge_always)
            upsertEdgeM (s_exp, simpl, edge_always)
            -- TODO technically it should only lead to knowing the first element
            -- if SPLIT() is contained within another expression
            -- simple leads to exp:
            case s_exp of
              CPrimitive (CONCAT (first:_)) _ -> do
                s_first <- foldCanonExpr first
                upsertEdgeM (simpl, s_first, edge_always)
                pure ()
              _ -> pure ()
            pure simpl
          CPrimitive (MAC key msg) _ -> do
            s_key <- foldCanonExpr key
            s_msg <- foldCanonExpr msg
            -- MAC produces a hash, so neither key/msg are leaked,
            -- but the attacker does get to reconstruct it if they know
            -- the key and the msg:
            upsertEdgePermutationsM [s_key,s_msg] simpl
            pure simpl
          CPrimitive (HKDF salt ikm info) _ -> do
            s_salt <- foldCanonExpr salt
            s_ikm <- foldCanonExpr ikm
            s_info <- foldCanonExpr info
            -- attacker can reconstruct this by knowing the args:
            upsertEdgePermutationsM [s_salt,s_ikm,s_info] simpl
            pure simpl
          CPrimitive (PW_HASH []) _ -> do
            upsertEdgeM (nil, simpl, edge_always)
            pure simpl
          CPrimitive (PW_HASH hash_lst) _ -> do
            simple_lst <- foldM (\acc exp -> do
                                     x <- foldCanonExpr exp
                                     pure (x:acc)
                                 ) [] hash_lst
            -- attacker can compute PW_HASH if it knows the args:
            upsertEdgePermutationsM simple_lst simpl
            pure simpl
          CPrimitive (SIGN key message) _ -> do
            s_key <- foldCanonExpr key
            s_msg <- foldCanonExpr message
            -- attacker can reconstruct from args:
            upsertEdgePermutationsM [s_key,s_msg] simpl
            pure simpl
          CPrimitive (SIGNVERIF pk message signed) _ -> do
            s_pk <- foldCanonExpr pk
            s_msg <- foldCanonExpr message
            s_signed <- foldCanonExpr signed
            upsertEdgePermutationsM [s_pk,s_msg,s_signed] simpl
            -- TODO not sure what the semantics for this is...
            -- TODO for now we let the attacker know the message regardless of the other parameters:
            upsertEdgeM (simpl, s_msg, edge_always)
            --case (s_pk, s_signed) of
            --  (CG key, SIGN key' message')
            --    | equivalenceExpr key key' && equivalenceExpr s_msg message' -> do
            --        upsertEdgeM (simpl, s_msg, Set.singleton $ Set.fromList [s_pk, signed])
            pure simpl
          CPrimitive (RINGSIGN key pk_b pk_c message) _ -> do
            -- TODO this one is fun, but complicated. TODO
            -- CG key,b,CG c,message => simpl
            -- CG key,CG b,c,message => simpl
            s_key <- foldCanonExpr key
            s_pk_b <- foldCanonExpr pk_b
            s_pk_c <- foldCanonExpr pk_c
            s_message <- foldCanonExpr message
            upsertEdgePermutationsM [s_key, s_pk_b, s_pk_c, s_message] simpl
            pure simpl
          CPrimitive (RINGSIGNVERIF a b c msg sig) _ -> do
            s_a <- foldCanonExpr a
            s_b <- foldCanonExpr b
            s_c <- foldCanonExpr c
            s_msg <- foldCanonExpr msg
            s_sig <- foldCanonExpr sig
            -- can reconstruct args:
            upsertEdgePermutationsM [s_a,s_b,s_c,s_msg,s_sig] simpl
            upsertEdgePermutationsM [a,b,c,msg,sig] simpl
            -- simpl leads to msg either way:
            upsertEdgeM (simpl, s_msg, edge_always)
            pure simpl -- TODO
          CPrimitive (BLIND k m) _ -> do
            s_k <- foldCanonExpr k
            s_m <- foldCanonExpr m
            -- reconstruct:
            upsertEdgePermutationsM [s_k,s_m] simpl
            -- TODO do we need more edges here?
            pure simpl
          CPrimitive (UNBLIND key msg signed) _ -> do
            s_key <- foldCanonExpr key
            s_msg <- foldCanonExpr msg
            s_signed <- foldCanonExpr signed
            -- reconstruct:
            upsertEdgePermutationsM [s_key,s_msg,s_signed] simpl
            case s_signed of
              CPrimitive (SIGN a (CPrimitive (BLIND k m) _)) _
                | equivalenceExpr s_key k && equivalenceExpr s_msg m -> do
                    signa <- foldCanonExpr (CPrimitive (SIGN a m) HasntQuestionMark)
                    upsertEdgeM (simpl, signa, edge_always)
              _ -> pure ()
            pure simpl -- TODO
          CPrimitive (SHAMIR_SPLIT exp) _ -> do -- TODO wtf, removing the "do" here results in a parse error on line 164 ??????
            s_exp <- foldCanonExpr exp
            -- exp leads to SHAMIR_SPLIT(exp)
            upsertEdgeM (s_exp, simpl, edge_always)
            -- simpl leads to each of the shares
            let share0 = CItem 0 simpl
                share1 = CItem 1 simpl
                share2 = CItem 2 simpl
            upsertMapNodeM share0
            upsertMapNodeM share1
            upsertMapNodeM share2
            upsertEdgeM (simpl, share0, edge_always)
            upsertEdgeM (simpl, share1, edge_always)
            upsertEdgeM (simpl, share2, edge_always)
            -- TODO here we simulate SHAMIR_JOIN, should we instead
            -- construct a SHAMIR_JOIN node for each permutation
            -- and add edges accordingly?
            -- let sj0 = CPrimitive (SHAMIR_JOIN share0 share1) HasntQuestionMark
            --     sj1 = CPrimitive (SHAMIR_JOIN share0 share2) HasntQuestionMark
            --     sj2 = CPrimitive (SHAMIR_JOIN share1 share2) HasntQuestionMark
            --
            upsertEdgePermutationsM [share0, share1, share2] s_exp
            pure simpl
          CPrimitive (SHAMIR_JOIN a b) _ -> do
            -- TODO this is pretty dodgy
            s_a <- foldCanonExpr a
            s_b <- foldCanonExpr b
            upsertEdgePermutationsM [s_a,s_b] simpl
            case (s_a,s_b) of
              (CItem na (CPrimitive (SHAMIR_SPLIT exp1) _),
               CItem nb (CPrimitive (SHAMIR_SPLIT exp2) _))
                | na /= nb && equivalenceExpr exp1 exp2 -> do
                    -- the idea here is that if they have two different (na/=nb)
                    -- pieces of the secret,
                    -- they get to know the secret (exp1 + exp2).
                    upsertEdgeM (simpl, exp1, edge_always)
                    upsertEdgeM (simpl, exp2, edge_always)
              _ -> pure () -- learn nothing
            pure simpl
          CPrimitive (PKE_ENC pk plaintext) _ -> do
            s_pk <- foldCanonExpr pk
            s_plaintext <- foldCanonExpr plaintext
            upsertEdgePermutationsM [s_plaintext, s_pk] simpl
            case s_pk of
              CG secret -> do
                -- attacker can decrypt if the know secret and simpl:
                upsertEdgePermutationsM [secret,simpl] s_plaintext
                -- attacker can re-encrypt if they know secret and message:
                upsertEdgePermutationsM [secret,s_plaintext] simpl
                pure simpl
              _ -> pure simpl -- TODO this should be a type error?
          CPrimitive (PKE_DEC key ciphertext) _ -> do
            s_key <- foldCanonExpr key
            s_ciphertext <- foldCanonExpr ciphertext
            -- reconstruct from args:
            upsertEdgePermutationsM [s_key,s_ciphertext] simpl
            -- re-encrypt:
            upsertEdgePermutationsM [simpl,s_key] s_ciphertext
            pure simpl
  foldM_ (\st (const,_knowledge) -> do
            let c_expr = canonicalizeExpr constmap (EConstant const)
            _ <- foldCanonExpr c_expr
            pure st
        ) () (Map.assocs constmap)
  foldM_ (\() (principalName, principalMap) -> do
            let cprName = CConstant (Constant principalName) CPrivate
            upsertMapNodeM cprName
            foldM (\() (c,(knowledge,_counter)) -> do
                      let c_expr = canonicalizeExpr constmap (EConstant c)
                      simpl <- foldCanonExpr c_expr
                      upsertEdgeM (cprName,c_expr,edge_always)
                      case knowledge of
                        Leaks -> do
                          -- attacker learns it because it's leaked:
                          upsertEdgeM (leaks, simpl, Set.singleton $ Set.singleton attacker)
                          pure ()
                        Received _ -> do
                          -- attacker learns it from the wire:
                          upsertEdgeM (sent, simpl, Set.singleton $ Set.singleton attacker)
                          pure ()
                        _ -> pure ()
                  ) () $ Map.assocs principalMap
            pure () ) () $ Map.assocs $ msPrincipalConstants ms
  (_nm, g) <- get
  -- TODO FIXME: unclear if we need this; probably not:
  foldM (\() (_n,v) -> case v of
            CPrimitive p HasQuestionMark -> do
              let unquestioned = (CPrimitive p HasntQuestionMark)
              upsertMapNodeM unquestioned
              upsertEdgeM (unquestioned,v,edge_always)
              upsertEdgeM (v,unquestioned,edge_always)
            _ -> pure ()) () (labNodes g)
  addPasswordBruteforceEdges
  (_nm, g) <- get
  case Data.Graph.Inductive.Query.DFS.isConnected g of
    True -> pure ()
  pure ()
  -- TODO FIXME assert that Data.Graph.Inductive.Query.DFS.isConnected g holds
  -- for the monad result (_, g) <- get  ; ie that we didn't add nodes that can't
  -- be reached from any of the other nodes.

process :: Model -> ModelState
process model =
  execState (processM model) emptyModelState

processM :: Model -> State ModelState ()
processM Model{..} = do
  mapM_ processModelPart modelParts

addWeightToEdges :: Context CanonExpr (Set (Set CanonExpr)) -> MContext CanonExpr PT
addWeightToEdges (b_in,a,c,b_out) =
  let b_in' :: Adj PT
      b_in' = Data.List.map (\(s,n) -> (PT (1,s),n)) b_in
      b_out' :: Adj PT
      b_out' = Data.List.map (\(s,n) -> (PT (1,s),n)) b_out
  in Just (b_in',a,c,b_out')

edgeMap :: Gr a b -> Map (Node, Node) b
edgeMap g = ufold (
  \(b_in, v_node, _, b_out) acc -> do
    let acc2 = foldl' (\acc2' (e,n) -> Map.insert (n     , v_node) e acc2') acc b_in
        acc3 = foldl' (\acc3' (e,n) -> Map.insert (v_node, n) e      acc3') acc2 b_out
      in acc3
  ) Map.empty g
restoreEdges :: Gr a (Set (Set CanonExpr)) -> Context a () -> MContext a (Set (Set CanonExpr))
restoreEdges g (b_in,v_node,v_label,b_out) =
  let findLabels f lst =
        Data.List.foldl' (
        \acc ((),n) -> case (acc, (Map.lookup (f n) (edgeMap g))) of
          (Nothing, _) -> Nothing
          (_, Nothing) -> Nothing
          (Just adjs, Just eset) -> Just ((eset,n):adjs)
        ) (Just []) lst
      b_in' :: Maybe (Adj (Set (Set CanonExpr)))
      b_in'  = findLabels (\e_node -> (e_node,v_node)) b_in
      b_out' = findLabels (\e_node -> (v_node,e_node)) b_out
  in case (b_in', b_out') of
    (Nothing, _) -> Nothing
    (_, Nothing) -> Nothing
    (Just in_adj, Just out_adj) -> Just (in_adj,v_node,v_label,out_adj)

-- computes the set of all expr reachable by the given principal.
-- the attacker is called "attacker" TODO
computePrincipalKnowledge :: Text -> State ModelState ()
computePrincipalKnowledge principalName = do
  g <- gets msConfidentialityGraph
  let ug = unOrdGr g
      attacker_reachable_n = Data.Graph.Inductive.Query.DFS.reachable attacker ug
      g_attacker_reachable = subgraph attacker_reachable_n ug
      reachable_edges = labEdges g_attacker_reachable
      reachable_nodes = labNodes g_attacker_reachable
      -- computing trc was an elegant solution, but it requires us to do bookkeping
      -- for each of the transitively collapsed edges such that
      --   a [[1],  [2]  ] -> b[[3]] -> c
      -- becomes
      --   a [[1],  [2]  ] -> b
      --   a [[1,3],[2,3]] -> c
      -- that would likely result in a considerable speedup.
      -- keeping the old stuff commented-out here:
      --g_trc = Data.Graph.Inductive.Query.TransClos.trc ug
      --g_attacker_might_trc :: Gr CanonExpr ()
      --g_attacker_might_trc = subgraph (neighbors g_trc attacker) g_trc
      --g_attacker_might = gfiltermap (restoreEdges (unOrdGr g)) g_attacker_might_trc
      attackerConst = CConstant (Constant principalName) CPrivate
      -- TODO this is kind of awkward; ideally we should use the NodeMap to look it
      -- up; but looking things up there is also awkward:
      attackerL = labfilter ((==) attackerConst) ug
      attacker = case nodes attackerL of
        [n] -> n
        _ -> 1 -- TODO this should never be reached
      learn_from_graph :: Set CanonExpr -> (Set CanonExpr, Gr CanonExpr (Set (Set CanonExpr)))
      learn_from_graph currently_known =
        -- TODO if attacker can find a path to a (CConstant _ CPassword)
        -- that does not go through a PW_HASH iteration, that means the attacker
        -- can bruteforce it.
        let known_edges = Data.List.filter (
              \(_,_,preconditions) -> any (`Set.isSubsetOf` currently_known
                                          ) preconditions) reachable_edges
            maybe_graph = mkGraph reachable_nodes known_edges
            now_reachable =
              Data.Graph.Inductive.Query.DFS.reachable attacker maybe_graph
            known_graph = subgraph now_reachable maybe_graph
            new_known = Set.fromList $ Data.List.map snd (labNodes known_graph)
        in (new_known, known_graph) --(Set.union new_set currently_known, known_graph)
  let attackerSetOrigin = Set.fromList [
        attackerConst
        , CConstant (Constant "nil") CPublic
        ]
      while_new old =
        let (newer, new_gr) = learn_from_graph old in
          if old == newer
          then (old, new_gr) -- nothing new learned, we are done
          else while_new newer -- we learned something new, try again
      (latest_attacker_knowl, filteredGraph) = while_new attackerSetOrigin
  mpcgm <- gets msPrincipalConfidentialityGraph
  mpcs <- gets msPrincipalConfidentialitySet
  modify $ \st -> do
    st{ msPrincipalConfidentialityGraph = Map.insert principalName (OrdGr filteredGraph) mpcgm
      , msPrincipalConfidentialitySet = Map.insert principalName latest_attacker_knowl mpcs
      }

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
    () <- computePrincipalKnowledge "attacker" -- TODO currently this is hardcoded so we don't do it for the other principals

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
      Just knowledge -> do
        upsertPrincipalConstant "attacker" cconst knowledge
        upsertPrincipalConstant receiver cconst knowledge
    -- TODO add consts to attacker knowledge

processModelPart (ModelPhase (phase)) = do
  count <- getCounter
  modify (
    \st -> st{msPhases = msPhases st ++ [(phase, count)]})

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
  let cexpr = canonicalizeExpr (Map.map fst prMap) expr
      constr ctr = do
        case cexpr of
          CPrimitive (SPLIT {}) _ -> EItem ctr expr
          CPrimitive (HKDF {}) _ -> EItem ctr expr
          CPrimitive (SHAMIR_SPLIT {}) _ -> EItem ctr expr
          -- TODO should we do this anytime lhs is a list of length > 1 ?
          _ -> expr
  case cexpr of
    CPrimitive (ASSERT a_e1 a_e2) _ | equivalenceExpr a_e1 a_e2 -> pure () -- succeeded
    CPrimitive (ASSERT a_e1 a_e2) _ -> addError (AssertionFailed a_e1 a_e2)
    _ -> pure ()
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
              upsertPrincipalConstant "attacker" constant Leaks
            (Just oldknowledge, _, True)
              | oldknowledge == knowledge ->
                upsertPrincipalConstant principalName constant knowledge
            (Just _, _, _) -> addError (OverlappingConstant constant)
            _ -> case True of -- crash
                   False -> addError (OverlappingConstant constant)
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
  constmap <- gets msConstants
  knowl_sets <- gets msPrincipalConfidentialitySet
  let canon_constant :: CanonExpr
      canon_constant = simplifyExpr $ canonicalizeExpr constmap (EConstant (constant))
      result = case Map.lookup "attacker" knowl_sets of
        Just attackerSet -> Set.notMember canon_constant attackerSet
        Nothing -> False
  addQueryResult query result
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
    CPrimitive (SHAMIR_JOIN
                ( CItem idxa (CPrimitive (SHAMIR_SPLIT e_a) _))
                ( CItem idxb (CPrimitive (SHAMIR_SPLIT e_b)_))
               ) hasq
      | not skipPrimitive && idxa /= idxb && equivalenceExpr e_a e_b ->
        -- TODO may need simplifyExpr e_a
        -- TODO may need to sort e_a,e_b and return a deterministic element
        simplifyExpr e_a
    --
    CPrimitive (SPLIT (CPrimitive (CONCAT (hd:_)) _)) _
      | not skipPrimitive -> simplifyExpr hd -- TODO is it correct to throw away the rest?
    --CPrimitive (CONCAT [
    --               CPrimitive (SPLIT
    --                           (CPrimitive (CONCAT lst) _TODOhasq)
    --                          ) _
    --                   ]) hasq -> CPrimitive (CONCAT lst) hasq
    -- UNBLIND(k, m, SIGN(a, BLIND(k, m))): SIGN(a, m)
    CPrimitive (UNBLIND k m (CPrimitive (SIGN a (CPrimitive (BLIND k2 m2) hasq'')) hasq')) hasq
      | not skipPrimitive -> do
      let s_k = simplifyExpr k
          s_m = simplifyExpr m
          s_a = simplifyExpr a
          s_k2 = simplifyExpr k2
          s_m2 = simplifyExpr m2
      if (equivalenceExpr s_k s_k2) && (equivalenceExpr s_m s_m2)
      then (CPrimitive (SIGN s_a s_m) HasntQuestionMark)
      else (CPrimitive (UNBLIND s_k s_m (CPrimitive (SIGN s_a (CPrimitive (BLIND s_k2 s_m2) HasntQuestionMark)) HasntQuestionMark)) HasntQuestionMark)
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
         else (CPrimitive (SIGNVERIF simple_g_key simple_message (CPrimitive (SIGN simple_key simple_message') HasntQuestionMark)) HasntQuestionMark)

    -- DEC(k, ENC(k, payload)) -> payload
    CPrimitive (DEC key encrypted) hasq | not skipPrimitive -> do
      let simple_enc = simplifyExpr encrypted
          simple_key = simplifyExpr key
      case simple_enc of
        -- remove the key:
        CPrimitive (ENC simple_key' payload) _
          | equivalenceExpr simple_key simple_key' -> simplifyExpr payload
        _ -> CPrimitive (DEC simple_key simple_enc) HasntQuestionMark
    -- AEAD_DEC(k, AEAD_ENC(k, payload, ad), ad) -> payload
    CPrimitive (AEAD_DEC key encrypted ad) _hasq
      | not skipPrimitive-> do
      let simple_enc = simplifyExpr encrypted
          simple_key = simplifyExpr key
          simple_ad  = simplifyExpr ad
      case simple_enc of
        -- remove the dec(enc()) if key and ad match:
        CPrimitive (AEAD_ENC simple_key' payload simple_ad') _
          | equivalenceExpr simple_key simple_key' && equivalenceExpr simple_ad simple_ad' -> simplifyExpr payload
        _ -> CPrimitive (AEAD_DEC simple_key simple_enc simple_ad) HasntQuestionMark
    -- TODO may need: CPrimitive ep hasq -> CPrimitive (mapPrimitiveP ep simplifyExpr) hasq
    CPrimitive p _hq | skipPrimitive -> simplifyExpr' False (CPrimitive (mapPrimitiveP p (simplifyExpr)) HasntQuestionMark)
    CPrimitive p hq -> CPrimitive p HasntQuestionMark
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

-- TODO would be nice with a test case that checks that equivalencePrimitive
-- TODO agrees with equivalenceExpr
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
        let (aux2,args) = foldl' (
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
  let dolist = foldl' (\acc exp -> foldConstantsInExpr acc exp f) acc in
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
