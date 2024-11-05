{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Monad.State.Strict (MonadState, State, runState)
import Data.Foldable (foldl', toList)
import Data.Functor.Foldable (Base, Recursive (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.String (IsString)
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.MultiMap (IntLikeMultiMap)
import IntLike.MultiMap qualified as ILMM
import IntLike.Set qualified as ILS
import Optics (Lens', Traversal, equality', traversalVL, traverseOf)
import Tang.Util (modifyML, stateML)

newtype NatTrans f g = NatTrans {runNatTrans :: forall a. f a -> g a}

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

type Path = Seq Seg

data Con = ConEq !Path !Path
  deriving stock (Eq, Ord, Show)

data Edge a = Edge !(Maybe Label) !a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type LabelIxMap = Map Label ChildIx

type IxLabelMap = IntLikeMap ChildIx Label

data SymbolInfo a = SymbolInfo
  { siLabelIx :: !LabelIxMap
  , siIxLabel :: !IxLabelMap
  , siIxValue :: !(Seq a)
  }
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

siArity :: SymbolInfo a -> Int
siArity = Seq.length . siIxValue

constantSymbolInfo :: SymbolInfo a
constantSymbolInfo = SymbolInfo Map.empty ILM.empty Seq.empty

mkSymbolInfo :: (Foldable f) => f (Edge a) -> SymbolInfo a
mkSymbolInfo = snd . foldl' go (0, constantSymbolInfo)
 where
  go (ix, SymbolInfo labIx ixLab ixVal) (Edge ml a) =
    let (labIx', ixLab') = maybe (labIx, ixLab) (\l -> (Map.insert l ix labIx, ILM.insert ix l ixLab)) ml
    in  (succ ix, SymbolInfo labIx' ixLab' (ixVal :|> a))

siFoldlChildren :: b -> SymbolInfo a -> (b -> ChildIx -> Maybe Label -> a -> b) -> b
siFoldlChildren b0 (SymbolInfo _ ixLab ixVal) f = snd (foldl' go (0, b0) ixVal)
 where
  go (ix, b) a = (succ ix, f b ix (ILM.lookup ix ixLab) a)

data SymbolNode c a = SymbolNode
  { snConstraints :: !(Seq c)
  , snInfo :: !(SymbolInfo a)
  }
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq a) => Eq (SymbolNode c a)

deriving stock instance (Ord c, Ord a) => Ord (SymbolNode c a)

deriving stock instance (Show c, Show a) => Show (SymbolNode c a)

snConTrav :: Traversal (SymbolNode c a) (SymbolNode d a) c d
snConTrav = traversalVL (\g (SymbolNode cs si) -> fmap (`SymbolNode` si) (traverse g cs))

mkSymbolNode :: (Foldable f) => Seq c -> f (Edge a) -> SymbolNode c a
mkSymbolNode cs = SymbolNode cs . mkSymbolInfo

data Node c b a
  = NodeSymbol !(SymbolNode c a)
  | NodeUnion !(Seq a)
  | NodeIntersect !(Seq a)
  | NodeClone !b
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq b, Eq a) => Eq (Node c b a)

deriving stock instance (Ord c, Ord b, Ord a) => Ord (Node c b a)

deriving stock instance (Show c, Show b, Show a) => Show (Node c b a)

nodeBackTrav :: Traversal (Node c b a) (Node c e a) b e
nodeBackTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> pure (NodeSymbol sn)
  NodeUnion xs -> pure (NodeUnion xs)
  NodeIntersect xs -> pure (NodeIntersect xs)
  NodeClone n -> fmap NodeClone (g n)

nodeConTrav :: Traversal (Node c b a) (Node d b a) c d
nodeConTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> fmap NodeSymbol (traverseOf snConTrav g sn)
  NodeUnion xs -> pure (NodeUnion xs)
  NodeIntersect xs -> pure (NodeIntersect xs)
  NodeClone n -> pure (NodeClone n)

type OrigMap f = IntLikeMap NodeId (f (Edge NodeId))

type NodeMap c = IntLikeMap NodeId (Node c NodeId NodeId)

type ParentMap = IntLikeMultiMap NodeId NodeId

data NodeGraph f c = NodeGraph
  { ngNext :: !NodeId
  , ngOrigs :: !(OrigMap f)
  , ngNodes :: !(NodeMap c)
  , ngParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f (Edge NodeId))) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f (Edge NodeId))) => Show (NodeGraph f c)

emptyNodeGraph :: NodeGraph f c
emptyNodeGraph = NodeGraph 0 ILM.empty ILM.empty ILM.empty

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
updateParents :: NodeId -> SymbolInfo NodeId -> ParentMap -> ParentMap
updateParents a si par = siFoldlChildren par si (\pm _ _ n -> ILMM.insert n a pm)

-- private
fresh :: (GraphC f c s m) => m NodeId
fresh = stateML nodeGraphL (\ng -> let nx = ng.ngNext in pure (nx, ng {ngNext = succ nx}))

-- private
node' :: (GraphC f c s m) => NodeId -> Node c NodeId NodeId -> m ()
node' a b = do
  modifyML nodeGraphL $ \(NodeGraph nx om nm par) ->
    let nm' = ILM.insert a b nm
    in  pure (NodeGraph nx om nm' par)

node :: (GraphC f c s m) => Node c NodeId NodeId -> m NodeId
node b = do
  a <- fresh
  node' a b
  pure a

addRecursive :: (GraphC f c s m) => (m NodeId -> m a) -> m a
addRecursive f = do
  a <- fresh
  f (fresh >>= \c -> c <$ node' c (NodeClone a))

addSymbol :: (Traversable f, GraphC f c s m) => Seq c -> f (Edge NodeId) -> m NodeId
addSymbol cs fe =
  let si = mkSymbolInfo fe
      n = NodeSymbol (SymbolNode cs si)
  in  stateML nodeGraphL $ \(NodeGraph nx om nm par) ->
        let om' = ILM.insert nx fe om
            nm' = ILM.insert nx n nm
            par' = updateParents nx si par
        in  pure (nx, NodeGraph (succ nx) om' nm' par')

addUnion :: (GraphC f c s m) => NodeId -> NodeId -> m NodeId
addUnion i j = node (NodeUnion (Seq.fromList (ILS.toList (ILS.fromList [i, j]))))

addUnionAll :: (Foldable g, GraphC f c s m) => g NodeId -> m NodeId
addUnionAll = node . NodeUnion . Seq.fromList . ILS.toList . ILS.fromList . toList

addIntersect :: (GraphC f c s m) => NodeId -> NodeId -> m NodeId
addIntersect i j = node (NodeIntersect (Seq.fromList (ILS.toList (ILS.fromList [i, j]))))

addIntersectAll :: (Foldable g, GraphC f c s m) => g NodeId -> m NodeId
addIntersectAll = node . NodeIntersect . Seq.fromList . ILS.toList . ILS.fromList . toList

addTree :: (Recursive t, Base t ~ f, Traversable f, GraphC f c s m) => t -> m NodeId
addTree t = do
  fn <- traverse addTree (project t)
  addSymbol Empty (fmap (Edge Nothing) fn)
