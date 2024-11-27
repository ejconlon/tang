{-# LANGUAGE OverloadedStrings #-}

module Tang.Translate where

import Control.Monad (join, (>=>))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.State.Strict (State, execState, state)
import Control.Monad.Trans (lift)
import Control.Placeholder (todo)
import Data.Coerce (Coercible, coerce)
import Data.Foldable (foldl', for_, toList, traverse_)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Map qualified as IntLikeMap
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import ListT (ListT (..))
import Prettyprinter (Doc, defaultLayoutOptions, layoutSmart)
import Prettyprinter.Render.Text (renderStrict)
import Tang.Ecta (ChildIx (..), EqCon (..), IxEqCon, Node (..), NodeId (..), NodeMap, SymbolNode (..))
import Tang.Exp (Conv (..), Tm (..), Ty (..), Val, convInt, convNull, expVal, valExp)
import Tang.Solver
  ( InterpEnv (..)
  , InterpM
  , Model
  , SolveM
  , SolveSt
  , appM
  , assert
  , assertWith
  , defConst
  , defFun
  , defTy
  , defVar
  , defVars
  , model
  , runInterpM
  , solve
  , varM
  )
import Tang.Symbolic (Symbol (..), Symbolic (..), symPretty)
import Tang.Util (foldM', forWithIndex_)

ceilLog2 :: Int -> Int
ceilLog2 n = max 1 (ceiling @Double @Int (logBase 2 (fromIntegral n)))

toIntTm :: (Coercible y Int) => Ty -> y -> Tm
toIntTm ty = TmInt ty . coerce

fromIntTm :: (Coercible y Int) => Ty -> Tm -> Maybe y
fromIntTm ty = \case
  TmInt ty' i | ty' == ty -> Just (coerce i)
  _ -> Nothing

convIntTm :: (Coercible y Int) => Ty -> Conv x y -> Conv x Tm
convIntTm ty (Conv to from) = Conv (toIntTm ty . to) (fromIntTm ty >=> from)

data Codec x = Codec
  { codecTy :: !Ty
  , codecConv :: !(Conv x Tm)
  }

codecInt :: (Coercible y Int) => Int -> Conv x y -> Codec x
codecInt card conv =
  let ty = TyBv (ceilLog2 card)
  in  Codec ty (convIntTm ty conv)

codecNull :: Codec (Maybe x) -> Tm
codecNull = flip convTo Nothing . codecConv

encode :: Codec x -> x -> Tm
encode = convTo . codecConv

decode :: Codec x -> Tm -> Maybe x
decode = convFrom . codecConv

type DomMap = NodeMap Symbolic IxEqCon

type NodeCodec = Codec (Maybe NodeId)

mkNodeCodec :: DomMap -> NodeCodec
mkNodeCodec dm =
  let sz = IntLikeMap.size dm
  in  codecInt @NodeId (sz + 1) (convNull (coerce sz) convInt)

type SymCodec = Codec (Maybe Symbol)

data SL = SL !Int !(Map Symbol Int) !(IntMap Symbol)

mkSymLookups :: DomMap -> SL
mkSymLookups = foldl' go (SL 0 Map.empty IntMap.empty) . ILM.elems
 where
  go :: SL -> Node Symbolic IxEqCon -> SL
  go sl@(SL i m n) = \case
    NodeSymbol (SymbolNode _ _ _ (Symbolic s _) _) ->
      SL (i + 1) (Map.insert s i m) (IntMap.insert i s n)
    _ -> sl

mkSymCodec :: DomMap -> SymCodec
mkSymCodec dm =
  let SL sz m n = mkSymLookups dm
      to = (m Map.!)
      from = flip IntMap.lookup n
  in  codecInt @Int (sz + 1) (convNull sz (Conv to from))

type CixCodec = Codec ChildIx

maxArity :: DomMap -> Int
maxArity = foldl' (\a -> max a . ar) 0 . ILM.elems
 where
  ar = \case
    NodeSymbol (SymbolNode i _ _ _ _) -> i
    _ -> 1

mkCixCodec :: DomMap -> Codec ChildIx
mkCixCodec dm =
  let mar = maxArity dm
  in  codecInt @ChildIx (mar + 1) convInt

data Dom = Dom
  { nodeCodec :: !NodeCodec
  , symCodec :: !SymCodec
  , cixCodec :: !CixCodec
  }

mkDom :: DomMap -> Dom
mkDom dm = Dom (mkNodeCodec dm) (mkSymCodec dm) (mkCixCodec dm)

preamble :: Dom -> NodeId -> SolveM ()
preamble (Dom nc sc cc) nr = do
  defTy "nid" (Just (codecTy nc))
  defTy "sid" (Just (codecTy sc))
  defTy "cix" (Just (codecTy cc))

  defConst "nodeNull" "nid"
  defConst "symNull" "sid"
  defConst "nodeRoot" "nid"

  defVars ["node", "child"] "nid"
  defVar "index" "cix"
  defVar "sym" "sid"

  defFun "nodeArity" [("node", "nid")] "cix"
  defFun "nodeChild" [("node", "nid"), ("index", "cix")] "nid"
  defFun "nodeSym" [("node", "nid")] "sid"
  defFun "nodeSymChild" [("node", "nid"), ("index", "cix")] "nid"
  defFun "canBeChild" [("node", "nid"), ("index", "cix"), ("child", "nid")] TyBool

  -- Ax: Concretely define null and root constants
  assert $ TmEq "nodeNull" (codecNull nc)
  assert $ TmEq "symNull" (codecNull sc)
  assert $ TmEq "nodeRoot" (encode nc (Just nr))

  -- Ax: Null node has null sym
  assert $ TmEq (TmApp "nodeSym" ["nodeNull"]) "symNull"

  -- Ax: Null node is nullary
  assert $ TmEq (TmApp "nodeArity" ["nodeNull"]) (encode cc 0)

  -- Ax: Null node has null children
  assert $
    TmImplies
      (TmEq "nodeNull" "node")
      (TmEq "nodeNull" (TmApp "nodeChild" ["node", "index"]))

  -- Ax: Relevant nodes have relevant children (less than arity)
  assert $
    TmIff
      ( TmAnd
          [ TmNot (TmEq "nodeNull" "node")
          , TmLt "index" (TmApp "nodeArity" ["node"])
          ]
      )
      (TmNot (TmEq "nodeNull" (TmApp "nodeChild" ["node", "index"])))

  -- Ax: Root node is relevant
  assert $ TmNot (TmEq "nodeNull" "nodeRoot")

  -- Ax: Child nodes must be possible
  assert $
    TmImplies
      (TmEq (TmApp "nodeChild" ["node", "index"]) "child")
      (TmApp "canBeChild" ["node", "index", "child"])

  -- Ax: It is possible for any child node to be irrelevant
  assert $ TmApp "canBeChild" ["node", "index", "nodeNull"]

  -- Ax: If child node has sym defined, then it is a sym child
  assert $
    TmImplies
      (TmNot (TmEq "symNull" (TmApp "nodeSym" [TmApp "nodeChild" ["node", "index"]])))
      (TmEq (TmApp "nodeSymChild" ["node", "index"]) (TmApp "nodeChild" ["node", "index"]))

  -- Ax: If child node does not have a sym defined, then the sym child propagates up
  assert $
    TmIff
      (TmEq "symNull" (TmApp "nodeSym" [TmApp "nodeChild" ["node", "index"]]))
      (TmEq (TmApp "nodeSymChild" ["node", "index"]) (TmApp "nodeSymChild" [TmApp "nodeChild" ["node", "index"], "index"]))

encodeSymNode :: Dom -> NodeId -> SymbolNode Symbolic IxEqCon -> SolveM ()
encodeSymNode dom nid (SymbolNode _ _ _ _s@(Symbolic sym chi) cons) = do
  let nidTm = encode (nodeCodec dom) (Just nid)
      symTm = encode (symCodec dom) (Just sym)
      maxTm = encode (cixCodec dom) (ChildIx (Seq.length chi))

  -- liftIO (print s)
  -- liftIO (print maxTm)

  -- Ax: Sanity: The node symbol is not the null symbol
  assert $ TmNot (TmEq "symNull" symTm)

  -- Ax: Sanity: The node id is not the null id
  assert $ TmNot (TmEq "nodeNull" nidTm)

  -- Ax: Concretely define node symbol
  assert $ TmEq (TmApp "nodeSym" [nidTm]) symTm

  -- Ax: Concretely define arity
  assert $ TmEq (TmApp "nodeArity" [nidTm]) maxTm

  -- Ax: Each child can have one concrete solution
  forWithIndex_ chi $ \ix cid -> do
    let cixTm = encode (cixCodec dom) (ChildIx ix)
        cidTm = encode (nodeCodec dom) (Just cid)
    -- liftIO (print ix)
    -- liftIO (print cixTm)
    -- liftIO (print cid)
    -- liftIO (print cidTm)
    assert $ TmApp "canBeChild" [nidTm, cixTm, cidTm]

  -- Emit assertions for constraints
  for_ cons $ \(EqCon p1 p2) -> do
    let (v1, c1, t1) = unroll dom "x" nidTm p1
        (v2, c2, t2) = unroll dom "y" nidTm p2
        v3 = fmap (,"nid") (toList (v1 <> v2))
        t3 = TmImplies (TmAnd (toList (c1 <> c2))) (TmEq t1 t2)
    assertWith v3 t3

data S = S !String !Int !(Seq String) !(Seq Tm) !Tm

unroll :: Dom -> String -> Tm -> Seq ChildIx -> (Seq String, Seq Tm, Tm)
unroll dom pre tm path =
  case execState (unrollS dom tm path) (S pre 0 Seq.empty Seq.empty tm) of
    S _ _ vs cs tm' -> (vs, cs, tm')

unrollS :: Dom -> Tm -> Seq ChildIx -> State S ()
unrollS dom tm = \case
  Empty -> pure ()
  ix :<| path' -> do
    tm' <- state $ \(S a b c d _) ->
      let f = a ++ show b
          tm' = TmVar f
          tm'' = encode (cixCodec dom) ix
          tm''' = TmApp "nodeSymChild" [tm, tm'']
          d' = d :|> TmEq tm' tm'''
          s' = S a (b + 1) (c :|> f) d' tm'
      in  (tm', s')
    unrollS dom tm' path'

encodeUnionNode :: Dom -> NodeId -> IntLikeSet NodeId -> SolveM ()
encodeUnionNode dom nid ns = do
  let nidTm = encode (nodeCodec dom) (Just nid)
      maxTm = encode (cixCodec dom) 1
      zeroTm = encode (cixCodec dom) 0

  -- Ax: Sanity: The node id is not the null id
  assert $ TmNot (TmEq "nodeNull" nidTm)

  -- Ax: The node sym is the null sym
  assert $ TmEq "symNull" (TmApp "nodeSym" [nidTm])

  -- Ax: Concretely define arity
  assert $ TmEq (TmApp "nodeArity" [nidTm]) maxTm

  -- Ax: Any of the concrete nodes can be a child
  for_ (ILS.toList ns) $ \cid -> do
    let cidTm = encode (nodeCodec dom) (Just cid)
    assert $ TmApp "canBeChild" [nidTm, zeroTm, cidTm]

-- TODO Intersection requires that we work with possible worlds
encodeIntersectNode :: Dom -> NodeId -> IntLikeSet NodeId -> SolveM ()
encodeIntersectNode _dom _nid _ns = todo

encodeMap
  :: Dom
  -> DomMap
  -> SolveM ()
encodeMap dom = traverse_ (uncurry go) . ILM.toList
 where
  go nid = \case
    NodeSymbol sn -> encodeSymNode dom nid sn
    NodeUnion ns -> encodeUnionNode dom nid ns
    NodeIntersect ns -> encodeIntersectNode dom nid ns

translate :: DomMap -> NodeId -> SolveM Dom
translate dm nr = do
  let dom = mkDom dm
  preamble dom nr
  encodeMap dom dm
  pure dom

advance :: Dom -> ExtractMap -> SolveM Bool
advance dom em =
  case xmapNegate (encode (nodeCodec dom) . Just) em of
    Nothing -> pure True
    Just tm -> False <$ assert tm

type ExtractStream = ListT (ExceptT String IO) ExtractMap

stream :: SolveSt -> DomMap -> NodeId -> ExtractStream
stream ss dm nr = ListT goStart
 where
  goStart = do
    dom <- lift (solve ss (translate dm nr))
    goLoop dom
  goLoop dom = do
    mm <- solve ss model
    case mm of
      Nothing -> pure Nothing
      Just m ->
        case extract dom m of
          Left e -> throwError e
          Right x -> pure (Just (x, ListT (goAdvance dom x)))
  goAdvance dom x = do
    done <- solve ss (advance dom x)
    if done
      then pure Nothing
      else goLoop dom

streamUncons :: ExtractStream -> IO (Either String (Maybe (ExtractMap, ExtractStream)))
streamUncons (ListT m) = runExceptT m

streamShow :: ExtractStream -> IO (Maybe String, Set Text)
streamShow = go Set.empty
 where
  go !acc s = do
    ea <- streamUncons s
    case ea of
      Left e -> pure (Just e, acc)
      Right ma -> case ma of
        Nothing -> pure (Nothing, acc)
        Just (x, s') -> do
          let t = xmapText x
              acc' = Set.insert t acc
          go acc' s'

decodeAsVal :: String -> Codec x -> (Maybe x -> Maybe y) -> String -> Val -> InterpM y
decodeAsVal tyName cod exec msg v =
  maybe
    (throwError (unwords ["Error decoding", tyName ++ ":", msg, "(" ++ show v ++ ")"]))
    pure
    (exec (decode cod (valExp v)))

encodeAsVal :: (Show x) => String -> Codec x -> String -> x -> InterpM Val
encodeAsVal tyName cod msg x =
  maybe
    (throwError (unwords ["Error encoding", tyName ++ ":", msg, "(" ++ show x ++ ")"]))
    pure
    (expVal (encode cod x))

data ExtractMap = ExtractMap
  { emRoot :: !NodeId
  , emMap :: IntLikeMap NodeId (Either NodeId (Symbolic NodeId))
  }
  deriving stock (Eq, Ord, Show)

extractM :: Dom -> InterpM ExtractMap
extractM d = goTop ILM.empty
 where
  decodeNid = decodeAsVal "node id" (nodeCodec d) join
  decodeCix = decodeAsVal "child ix" (cixCodec d) id
  encodeCix = encodeAsVal "child ix" (cixCodec d)
  decodeSym msg x = fmap join (decodeAsVal "symbol" (symCodec d) Just msg x)
  goTop m = do
    rootV <- varM "nodeRoot"
    root <- decodeNid "root node" rootV
    (xmap, _) <- goLevel Set.empty m rootV
    pure (ExtractMap root xmap)
  goLevel s m parentV = do
    parent <- decodeNid "parent node" parentV
    if Set.member parent s
      then pure (m, s)
      else do
        let s' = Set.insert parent s
        ChildIx ar <- decodeCix "node arity" =<< appM "nodeArity" [parentV]
        if ar >= 0
          then do
            msym <- decodeSym "node sym" =<< appM "nodeSym" [parentV]
            (ea, m'', s'') <- case msym of
              Nothing ->
                if ar == 1
                  then do
                    zeroV <- encodeCix "zero ix" 0
                    choiceV <- appM "nodeChild" [parentV, zeroV]
                    choice <- decodeNid "choice node" choiceV
                    (m'', s'') <- goLevel s' m choiceV
                    pure (Left choice, m'', s'')
                  else throwError ("Bad sym for node: " ++ show parent)
              Just sym -> do
                (cs, m'', s'') <- foldM' (Empty, m, s') [0 .. ar - 1] $ \(cs, m'', s'') i -> do
                  ixV <- encodeCix "child ix" (ChildIx i)
                  childV <- appM "nodeChild" [parentV, ixV]
                  child <- decodeNid "child node" childV
                  (m''', s''') <- goLevel s'' m'' childV
                  pure (cs :|> child, m''', s''')
                pure (Right (Symbolic sym cs), m'', s'')
            pure (ILM.insert parent ea m'', s'')
          else throwError ("Bad arity for node: " ++ show parent)

extract :: Dom -> Model -> Either String ExtractMap
extract d m = runInterpM (extractM d) (InterpEnv m Map.empty)

xmapPretty :: ExtractMap -> Doc ann
xmapPretty (ExtractMap root xmap) = go root
 where
  go nid = case ILM.partialLookup nid xmap of
    Left cid -> go cid
    Right sym -> symPretty go sym

xmapText :: ExtractMap -> Text
xmapText = renderStrict . layoutSmart defaultLayoutOptions . xmapPretty

xmapNegate :: (NodeId -> Tm) -> ExtractMap -> Maybe Tm
xmapNegate enc (ExtractMap _ m) = go [] (ILM.toList m)
 where
  go !acc = \case
    [] -> case acc of
      [] -> Nothing
      _ -> Just (TmOr acc)
    (nid, ea) : xs ->
      case ea of
        Right _ -> go acc xs
        Left cid -> go (TmNot (TmEq (enc nid) (enc cid)) : acc) xs
