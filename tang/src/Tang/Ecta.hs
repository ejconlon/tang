{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Exception (Exception)
import Control.Monad.Except (Except, throwError)
import Control.Monad.State.Strict (MonadState, State, runState, state)
import Data.Foldable (foldl', traverse_)
import Data.Functor.Foldable (Base, Recursive (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.MultiMap (IntLikeMultiMap)
import IntLike.MultiMap qualified as ILMM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Lens', Traversal, equality', traversalVL, traverseOf)
import Tang.Util (mapSetM, modifyML, stateML)

newtype Label = Label {unLabel :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

newtype ChildIx = ChildIx {unChildIx :: Int}
  deriving newtype (Eq, Ord, Num, Enum)
  deriving stock (Show)

newtype NodeId = NodeId {unNodeId :: Int}
  deriving newtype (Eq, Ord, Num, Enum)
  deriving stock (Show)

data Seg = SegLabel !Label | SegIndex !ChildIx
  deriving stock (Eq, Ord, Show)

type SegPath = Seq Seg

type IxPath = Seq ChildIx

data EqCon p = EqCon !p !p
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type SegEqCon = EqCon SegPath

type IxEqCon = EqCon IxPath

eqConT :: Traversal SegEqCon IxEqCon Seg ChildIx
eqConT = traversalVL (\g (EqCon p q) -> liftA2 EqCon (traverse g p) (traverse g q))

data Edge = Edge !(Maybe Label) !NodeId
  deriving stock (Eq, Ord, Show)

type LabelIxMap = Map Label ChildIx

type IxLabelMap = IntLikeMap ChildIx Label

data SymbolNode f c = SymbolNode
  { snArity :: !Int
  , snLabelIx :: !LabelIxMap
  , snIxLabel :: !IxLabelMap
  , snStructure :: !(f NodeId)
  , snConstraints :: !(Set c)
  }

deriving stock instance (Eq c, Eq (f NodeId)) => Eq (SymbolNode f c)

deriving stock instance (Ord c, Ord (f NodeId)) => Ord (SymbolNode f c)

deriving stock instance (Show c, Show (f NodeId)) => Show (SymbolNode f c)

-- private
data X = X !ChildIx !LabelIxMap !IxLabelMap

mkSymbolNode :: (Traversable f) => f Edge -> Set c -> SymbolNode f c
mkSymbolNode fe cs = goStart
 where
  goStart =
    let x0 = X 0 Map.empty ILM.empty
        (fn, X (ChildIx ar) labIx ixLab) = runState (traverse goChild fe) x0
    in  SymbolNode ar labIx ixLab fn cs
  goChild (Edge ml a) = state $ \(X ix labIx ixLab) ->
    let (labIx', ixLab') = maybe (labIx, ixLab) (\l -> (Map.insert l ix labIx, ILM.insert ix l ixLab)) ml
        x = X (succ ix) labIx' ixLab'
    in  (a, x)

snMapConM :: (Monad m, Ord d) => (c -> m d) -> SymbolNode f c -> m (SymbolNode f d)
snMapConM f (SymbolNode labIx ixLab ixNode struct cs) = fmap (SymbolNode labIx ixLab ixNode struct) (mapSetM f cs)

snMapConM_ :: (Monad m) => (c -> m ()) -> SymbolNode f c -> m ()
snMapConM_ f sn = traverse_ f (snConstraints sn)

snFoldlChildren :: (Foldable f) => b -> SymbolNode f c -> (b -> ChildIx -> Maybe Label -> NodeId -> b) -> b
snFoldlChildren b0 (SymbolNode _ _ ixLab fn _) f = snd (foldl' go (0, b0) fn)
 where
  go (ix, b) a = (succ ix, f b ix (ILM.lookup ix ixLab) a)

newtype RewriteErr = RewriteErr Label
  deriving stock (Eq, Ord, Show)

instance Exception RewriteErr

-- TODO report path to label
snRewriteSeg :: (Ord d) => Traversal c d Seg ChildIx -> SymbolNode f c -> Except RewriteErr (SymbolNode f d)
snRewriteSeg t = goStart
 where
  goStart (SymbolNode ar labIx ixLab struct cons) = do
    cons' <- mapSetM (goCon labIx) cons
    pure (SymbolNode ar labIx ixLab struct cons')
  goCon = traverseOf t . goSeg
  goSeg labIx = \case
    SegLabel lab -> maybe (throwError (RewriteErr lab)) pure (Map.lookup lab labIx)
    SegIndex ix -> pure ix

data Node f c
  = NodeSymbol !(SymbolNode f c)
  | NodeUnion !(IntLikeSet NodeId)
  | NodeIntersect !(IntLikeSet NodeId)
  | NodeClone !NodeId

deriving stock instance (Eq c, Eq (f NodeId)) => Eq (Node f c)

deriving stock instance (Ord c, Ord (f NodeId)) => Ord (Node f c)

deriving stock instance (Show c, Show (f NodeId)) => Show (Node f c)

nodeMapSymM_ :: (Monad m) => (SymbolNode f c -> m ()) -> Node f c -> m ()
nodeMapSymM_ f = \case
  NodeSymbol sn -> f sn
  _ -> pure ()

nodeMapSymM :: (Monad m) => (SymbolNode f c -> m (SymbolNode g d)) -> Node f c -> m (Node g d)
nodeMapSymM f = \case
  NodeSymbol sn -> fmap NodeSymbol (f sn)
  NodeUnion xs -> pure (NodeUnion xs)
  NodeIntersect xs -> pure (NodeIntersect xs)
  NodeClone n -> pure (NodeClone n)

type NodeMap f c = IntLikeMap NodeId (Node f c)

type ParentMap = IntLikeMultiMap NodeId NodeId

data NodeGraph f c = NodeGraph
  { ngNextNid :: !NodeId
  , ngNodes :: !(NodeMap f c)
  , ngParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f NodeId)) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f NodeId)) => Show (NodeGraph f c)

emptyNodeGraph :: NodeGraph f c
emptyNodeGraph = NodeGraph 0 ILM.empty ILM.empty

ngMapNodeM_ :: (Monad m) => (Node f c -> m ()) -> NodeGraph f c -> m ()
ngMapNodeM_ f = traverse_ f . ngNodes

ngMapNodeM :: (Monad m) => (Node f c -> m (Node g d)) -> NodeGraph f c -> m (NodeGraph g d)
ngMapNodeM f (NodeGraph x y z) = fmap (\y' -> NodeGraph x y' z) (traverse f y)

-- TODO report failing node id
ngRewriteSeg :: (Ord d) => Traversal c d Seg ChildIx -> NodeGraph f c -> Except RewriteErr (NodeGraph f d)
ngRewriteSeg = ngMapNodeM . nodeMapSymM . snRewriteSeg

class HasNodeGraph f c s | s -> f c where
  nodeGraphL :: Lens' s (NodeGraph f c)

instance HasNodeGraph f c (NodeGraph f c) where
  nodeGraphL = equality'

type GraphM f c = State (NodeGraph f c)

runGraphM :: GraphM f c a -> NodeGraph f c -> (a, NodeGraph f c)
runGraphM = runState

buildGraph :: GraphM f c NodeId -> (NodeId, NodeGraph f c)
buildGraph = flip runGraphM emptyNodeGraph

type GraphC f c s m = (HasNodeGraph f c s, MonadState s m)

-- private
updateParents :: (Foldable f) => NodeId -> SymbolNode f c -> ParentMap -> ParentMap
updateParents a si par = snFoldlChildren par si (\pm _ _ n -> ILMM.insert n a pm)

-- private
mkFreshNodeId :: (GraphC f c s m) => m NodeId
mkFreshNodeId = stateML nodeGraphL (\ng -> let nx = ng.ngNextNid in pure (nx, ng {ngNextNid = succ nx}))

-- private
addNode' :: (GraphC f c s m) => NodeId -> Node f c -> m ()
addNode' a b = do
  modifyML nodeGraphL $ \(NodeGraph nx nm par) ->
    let nm' = ILM.insert a b nm
    in  pure (NodeGraph nx nm' par)

addNode :: (GraphC f c s m) => Node f c -> m NodeId
addNode b = do
  a <- mkFreshNodeId
  addNode' a b
  pure a

addRecursive :: (GraphC f c s m) => (m NodeId -> m a) -> m a
addRecursive f = do
  a <- mkFreshNodeId
  f (mkFreshNodeId >>= \c -> c <$ addNode' c (NodeClone a))

addSymbol :: (Traversable f, GraphC f c s m) => f Edge -> Set c -> m NodeId
addSymbol fe cs =
  let sn = mkSymbolNode fe cs
  in  stateML nodeGraphL $ \(NodeGraph nx nm par) ->
        let nm' = ILM.insert nx (NodeSymbol sn) nm
            par' = updateParents nx sn par
        in  pure (nx, NodeGraph (succ nx) nm' par')

addUnion :: (GraphC f c s m) => NodeId -> NodeId -> m NodeId
addUnion i j = addUnionAll (ILS.fromList [i, j])

addUnionAll :: (GraphC f c s m) => IntLikeSet NodeId -> m NodeId
addUnionAll = addNode . NodeUnion

addIntersect :: (GraphC f c s m) => NodeId -> NodeId -> m NodeId
addIntersect i j = addIntersectAll (ILS.fromList [i, j])

addIntersectAll :: (GraphC f c s m) => IntLikeSet NodeId -> m NodeId
addIntersectAll = addNode . NodeIntersect

addTree :: (Recursive t, Base t ~ f, Traversable f, GraphC f c s m) => t -> m NodeId
addTree t = do
  fn <- traverse addTree (project t)
  addSymbol (fmap (Edge Nothing) fn) Set.empty
