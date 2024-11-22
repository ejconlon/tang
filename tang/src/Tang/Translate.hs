{-# LANGUAGE OverloadedStrings #-}

module Tang.Translate where

import Control.Monad ((>=>))
import Control.Placeholder (todo)
import Data.Coerce (Coercible, coerce)
import Data.Foldable (foldl', traverse_)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import IntLike.Map qualified as ILM
import IntLike.Map qualified as IntLikeMap
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Tang.Ecta (ChildIx (..), EqCon (..), IxEqCon, Node (..), NodeId (..), NodeMap, SymbolNode (..))
import Tang.Exp (Tm (..), Ty (..))
import Tang.Solver (SolveM, assert, defConst, defFun, defTy, defVar, defVars)
import Tang.Symbolic (Symbol (..), Symbolic (..))
import Tang.Util (forWithIndex_)

ceilLog2 :: Int -> Int
ceilLog2 n = ceiling @Double @Int (logBase 2 (fromIntegral n))

toIntTm :: (Coercible y Int) => Ty -> y -> Tm
toIntTm ty = TmInt ty . coerce

fromIntTm :: (Coercible y Int) => Ty -> Tm -> Maybe y
fromIntTm ty = \case
  TmInt ty' i | ty' == ty -> Just (coerce i)
  _ -> Nothing

data Conv x y = Conv
  { convTo :: !(x -> y)
  , convFrom :: !(y -> Maybe x)
  }

convId :: Conv x x
convId = Conv id Just

convCompose :: Conv y z -> Conv x y -> Conv x z
convCompose (Conv toYZ fromYZ) (Conv toXY fromXY) = Conv (toYZ . toXY) (fromYZ >=> fromXY)

convInt :: (Coercible x Int, Coercible y Int) => Conv x y
convInt = Conv coerce (Just . coerce)

convNull :: (Eq y) => y -> Conv x y -> Conv (Maybe x) y
convNull nl (Conv to from) =
  Conv
    (maybe nl to)
    (\y -> if y == nl then Nothing else Just (from y))

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
  in  codecInt @ChildIx mar convInt

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

  -- Ax: Root node is relevant
  assert $ TmNot (TmEq "nodeNull" "nodeRoot")

  -- TODO fix bv lt
  -- -- Ax: Child indices must be less than max index
  -- assert $
  --   TmImplies
  --     (TmApp "canBeChild" ["node", "index", "child"])
  --     (TmLt "index" (TmApp "nodeArity" ["node"]))

  -- Ax: Child nodes must be possible
  assert $ TmApp "canBeChild" ["node", "index", TmApp "nodeChild" ["node", "index"]]

  -- Ax: Relevant nodes have relevant children and vice versa
  assert $
    TmIff
      (TmEq "nodeNull" "node")
      (TmEq "nodeNull" (TmApp "nodeChild" ["node", "index"]))

  -- Ax: Any node can be irrelevant
  assert $ TmApp "canBeChild" ["node", "index", "nodeNull"]

  -- Ax: If child node has sym defined, then it is a sym child
  assert $
    TmIff
      (TmNot (TmEq "symNull" (TmApp "nodeSym" [TmApp "nodeChild" ["node", "index"]])))
      (TmEq (TmApp "nodeSymChild" ["node", "index"]) (TmApp "nodeChild" ["node", "index"]))

  -- Ax: If child node does not have a sym defined, then the sym child propagates up
  assert $
    TmIff
      (TmEq "symNull" (TmApp "nodeSym" [TmApp "nodeChild" ["node", "index"]]))
      (TmEq (TmApp "nodeSymChild" ["node", "index"]) (TmApp "nodeSymChild" [TmApp "nodeChild" ["node", "index"], "index"]))

encodeSymNode :: Dom -> NodeId -> SymbolNode Symbolic IxEqCon -> SolveM ()
encodeSymNode dom nid (SymbolNode _ _ _ (Symbolic sym chi) cons) = do
  let nidTm = encode (nodeCodec dom) (Just nid)
      symTm = encode (symCodec dom) (Just sym)
      maxTm = encode (cixCodec dom) (ChildIx (Seq.length chi - 1))

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
    assert $ TmApp "canBeChild" [nidTm, cixTm, cidTm]

  -- TODO emit assertions for constraints
  forWithIndex_ cons $ \_ (EqCon _p1 _p2) ->
    todo

encodeUnionNode :: Dom -> NodeId -> IntLikeSet NodeId -> SolveM ()
encodeUnionNode dom nid ns = do
  let nidTm = encode (nodeCodec dom) (Just nid)
      zeroTm = encode (cixCodec dom) 0

  -- Ax: Sanity: The node id is not the null id
  assert $ TmNot (TmEq "nodeNull" nidTm)

  -- Ax: The node sym is the null sym
  assert $ TmEq "symNull" (TmApp "nodeSym" [nidTm])

  -- Ax: Any of the concrete nodes can be a child
  forWithIndex_ (ILS.toList ns) $ \_ cid -> do
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

translate :: DomMap -> NodeId -> SolveM ()
translate dm nr = do
  let dom = mkDom dm
  preamble dom nr
  encodeMap dom dm
