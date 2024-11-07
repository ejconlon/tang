{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Monad.State.Strict (MonadState, State, runState, state)
import Data.Foldable (foldl', traverse_)
import Data.Functor.Foldable (Base, Recursive (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
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
import Optics (Lens', equality')
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

data Edge = Edge !(Maybe Label) !NodeId
  deriving stock (Eq, Ord, Show)

type LabelIxMap = Map Label ChildIx

type IxLabelMap = IntLikeMap ChildIx Label

data SymbolNode f c = SymbolNode
  { snLabelIx :: !LabelIxMap
  , snIxLabel :: !IxLabelMap
  , snChildren :: !(Seq NodeId)
  , snStructure :: !(f ChildIx)
  , snConstraints :: !(Set c)
  }

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (SymbolNode f c)

deriving stock instance (Ord c, Ord (f ChildIx)) => Ord (SymbolNode f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (SymbolNode f c)

-- private
data X = X !ChildIx !LabelIxMap !IxLabelMap !(Seq NodeId)

mkSymbolNode :: (Traversable f) => f Edge -> Set c -> SymbolNode f c
mkSymbolNode fe cs = goStart
 where
  goStart =
    let x0 = X 0 Map.empty ILM.empty Empty
        (fi, X _ labIx ixLab ixVal) = runState (traverse goChild fe) x0
    in  SymbolNode labIx ixLab ixVal fi cs
  goChild (Edge ml a) = state $ \(X ix labIx ixLab ixVal) ->
    let (labIx', ixLab') = maybe (labIx, ixLab) (\l -> (Map.insert l ix labIx, ILM.insert ix l ixLab)) ml
        x = X (succ ix) labIx' ixLab' (ixVal :|> a)
    in  (ix, x)

snArity :: SymbolNode f c -> Int
snArity = Seq.length . snChildren

snMapConM :: (Monad m, Ord d) => (c -> m d) -> SymbolNode f c -> m (SymbolNode f d)
snMapConM f (SymbolNode labIx ixLab ixNode struct cs) = fmap (SymbolNode labIx ixLab ixNode struct) (mapSetM f cs)

snMapConM_ :: (Monad m) => (c -> m ()) -> SymbolNode f c -> m ()
snMapConM_ f sn = traverse_ f (snConstraints sn)

snFoldlChildren :: b -> SymbolNode f c -> (b -> ChildIx -> Maybe Label -> NodeId -> b) -> b
snFoldlChildren b0 (SymbolNode _ ixLab ixVal _ _) f = snd (foldl' go (0, b0) ixVal)
 where
  go (ix, b) a = (succ ix, f b ix (ILM.lookup ix ixLab) a)

data Node f c
  = NodeSymbol !(SymbolNode f c)
  | NodeUnion !(IntLikeSet NodeId)
  | NodeIntersect !(IntLikeSet NodeId)
  | NodeClone !NodeId

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (Node f c)

deriving stock instance (Ord c, Ord (f ChildIx)) => Ord (Node f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (Node f c)

nodeMapConM_ :: (Monad m) => (c -> m ()) -> Node f c -> m ()
nodeMapConM_ f = \case
  NodeSymbol sn -> snMapConM_ f sn
  _ -> pure ()

nodeMapConM :: (Monad m, Ord d) => (c -> m d) -> Node f c -> m (Node f d)
nodeMapConM f = \case
  NodeSymbol sn -> fmap NodeSymbol (snMapConM f sn)
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

deriving stock instance (Eq c, Eq (f ChildIx)) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f ChildIx)) => Show (NodeGraph f c)

emptyNodeGraph :: NodeGraph f c
emptyNodeGraph = NodeGraph 0 ILM.empty ILM.empty

ngMapConM_ :: (Monad m) => (c -> m ()) -> NodeGraph f c -> m ()
ngMapConM_ f = traverse_ (nodeMapConM_ f) . ngNodes

ngMapConM :: (Monad m, Ord d) => (c -> m d) -> NodeGraph f c -> m (NodeGraph f d)
ngMapConM f (NodeGraph x y z) = fmap (\y' -> NodeGraph x y' z) (traverse (nodeMapConM f) y)

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
updateParents :: NodeId -> SymbolNode f c -> ParentMap -> ParentMap
updateParents a si par = snFoldlChildren par si (\pm _ _ n -> ILMM.insert n a pm)

-- private
fresh :: (GraphC f c s m) => m NodeId
fresh = stateML nodeGraphL (\ng -> let nx = ng.ngNextNid in pure (nx, ng {ngNextNid = succ nx}))

-- private
node' :: (GraphC f c s m) => NodeId -> Node f c -> m ()
node' a b = do
  modifyML nodeGraphL $ \(NodeGraph nx nm par) ->
    let nm' = ILM.insert a b nm
    in  pure (NodeGraph nx nm' par)

node :: (GraphC f c s m) => Node f c -> m NodeId
node b = do
  a <- fresh
  node' a b
  pure a

addRecursive :: (GraphC f c s m) => (m NodeId -> m a) -> m a
addRecursive f = do
  a <- fresh
  f (fresh >>= \c -> c <$ node' c (NodeClone a))

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
addUnionAll = node . NodeUnion

addIntersect :: (GraphC f c s m) => NodeId -> NodeId -> m NodeId
addIntersect i j = addIntersectAll (ILS.fromList [i, j])

addIntersectAll :: (GraphC f c s m) => IntLikeSet NodeId -> m NodeId
addIntersectAll = node . NodeIntersect

addTree :: (Recursive t, Base t ~ f, Traversable f, GraphC f c s m) => t -> m NodeId
addTree t = do
  fn <- traverse addTree (project t)
  addSymbol (fmap (Edge Nothing) fn) Set.empty
