{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Monad.State.Strict (MonadState, State, runState)
import Data.Coerce (Coercible)
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
import Optics (Lens', Traversal, Traversal', equality', foldlOf', traversalVL, traverseOf)
import Tang.Util (modifyML, stateML)

newtype NatTrans f g = NatTrans {runNatTrans :: forall a. f a -> g a}

newtype Symbol = Symbol {unSymbol :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

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

data Con p = ConEq !p !p
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

data Edge a = Edge !(Maybe Label) !a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type LabelIxMap = Map Label ChildIx

type IxLabelMap = IntLikeMap ChildIx Label

data SymbolInfo a = SymbolInfo
  { siArity :: !Int
  , siLabelIx :: !LabelIxMap
  , siIxLabel :: !IxLabelMap
  , siIxValue :: !(Seq a)
  }
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

constantSymbolInfo :: SymbolInfo a
constantSymbolInfo = SymbolInfo 0 Map.empty ILM.empty Seq.empty

mkSymbolInfo :: (Foldable f) => f (Edge a) -> SymbolInfo a
mkSymbolInfo = snd . foldl' go (0, constantSymbolInfo)
 where
  go (ix, SymbolInfo ar labIx ixLab ixVal) (Edge ml a) =
    let (labIx', ixLab') = maybe (labIx, ixLab) (\l -> (Map.insert l ix labIx, ILM.insert ix l ixLab)) ml
    in  (succ ix, SymbolInfo (succ ar) labIx' ixLab' (ixVal :|> a))

data SymbolNode f c a = SymbolNode
  { snConstraints :: !(Seq c)
  , snInfo :: !(SymbolInfo a)
  , snSymbol :: !(f (Edge a))
  }
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq a, Eq (f (Edge a))) => Eq (SymbolNode f c a)

deriving stock instance (Ord c, Ord a, Ord (f (Edge a))) => Ord (SymbolNode f c a)

deriving stock instance (Show c, Show a, Show (f (Edge a))) => Show (SymbolNode f c a)

snConTrav :: Traversal (SymbolNode f c a) (SymbolNode f d a) c d
snConTrav = traversalVL (\g (SymbolNode cs si fe) -> fmap (\ds -> SymbolNode ds si fe) (traverse g cs))

snEdgeTrav :: (Traversable f) => Traversal' (SymbolNode f c a) (Edge a)
snEdgeTrav = traversalVL (\g (SymbolNode cs si fe) -> fmap (SymbolNode cs si) (traverse g fe))

snFoldEdges :: (Traversable f) => b -> SymbolNode f c a -> (b -> Edge a -> b) -> b
snFoldEdges b sn f = foldlOf' snEdgeTrav f b sn

snSymTrans :: (Foldable g) => NatTrans f g -> SymbolNode f c a -> SymbolNode g c a
snSymTrans nt (SymbolNode cs _ fe) =
  let ge = runNatTrans nt fe
      si = mkSymbolInfo ge
  in  SymbolNode cs si ge

mkSymbolNode :: (Foldable f) => Seq c -> f (Edge a) -> SymbolNode f c a
mkSymbolNode cs fe = SymbolNode cs (mkSymbolInfo fe) fe

data Node f c b a
  = NodeSymbol !(SymbolNode f c a)
  | NodeUnion !(Seq a)
  | NodeIntersect !(Seq a)
  | NodeClone !b
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq b, Eq a, Eq (f (Edge a))) => Eq (Node f c b a)

deriving stock instance (Ord c, Ord b, Ord a, Ord (f (Edge a))) => Ord (Node f c b a)

deriving stock instance (Show c, Show b, Show a, Show (f (Edge a))) => Show (Node f c b a)

nodeBackTrav :: Traversal (Node f c b a) (Node f c e a) b e
nodeBackTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> pure (NodeSymbol sn)
  NodeUnion xs -> pure (NodeUnion xs)
  NodeIntersect xs -> pure (NodeIntersect xs)
  NodeClone n -> fmap NodeClone (g n)

nodeConTrav :: Traversal (Node f c b a) (Node f d b a) c d
nodeConTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> fmap NodeSymbol (traverseOf snConTrav g sn)
  NodeUnion xs -> pure (NodeUnion xs)
  NodeIntersect xs -> pure (NodeIntersect xs)
  NodeClone n -> pure (NodeClone n)

nodeSymTrans :: (Foldable g) => NatTrans f g -> Node f c b a -> Node g c b a
nodeSymTrans nt = \case
  NodeSymbol sn -> NodeSymbol (snSymTrans nt sn)
  NodeUnion xs -> NodeUnion xs
  NodeIntersect xs -> NodeIntersect xs
  NodeClone n -> NodeClone n

union :: (Coercible a Int) => a -> a -> Node f c b a
union i j = NodeUnion (Seq.fromList (ILS.toList (ILS.fromList [i, j])))

unionAll :: (Foldable g, Coercible a Int) => g a -> Node f c b a
unionAll = NodeUnion . Seq.fromList . ILS.toList . ILS.fromList . toList

intersect :: (Coercible a Int) => a -> a -> Node f c b a
intersect i j = NodeIntersect (Seq.fromList (ILS.toList (ILS.fromList [i, j])))

intersectAll :: (Foldable g, Coercible a Int) => g a -> Node f c b a
intersectAll = NodeIntersect . Seq.fromList . ILS.toList . ILS.fromList . toList

type NodeMap f c = IntLikeMap NodeId (Node f c NodeId NodeId)

type ParentMap = IntLikeMultiMap NodeId NodeId

data NodeGraph f c = NodeGraph
  { ngRoot :: !NodeId
  , ngNodes :: !(NodeMap f c)
  , ngParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f (Edge NodeId))) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f (Edge NodeId))) => Show (NodeGraph f c)

data NodeSt f c = NodeSt
  { nsNext :: !NodeId
  , nsNodes :: !(NodeMap f c)
  , nsParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f (Edge NodeId))) => Eq (NodeSt f c)

deriving stock instance (Show c, Show (f (Edge NodeId))) => Show (NodeSt f c)

type NodeM f c = State (NodeSt f c)

runNodeM :: NodeM f c a -> NodeSt f c -> (a, NodeSt f c)
runNodeM = runState

buildGraph :: NodeM f c NodeId -> NodeGraph f c
buildGraph m =
  let (r, NodeSt _ nm par) = runState m (NodeSt 0 ILM.empty ILM.empty)
  in  NodeGraph r nm par

class HasNodeSt f c s | s -> f c where
  nodeStL :: Lens' s (NodeSt f c)

instance HasNodeSt f c (NodeSt f c) where
  nodeStL = equality'

type NodeC f c s m = (HasNodeSt f c s, MonadState s m)

-- private
processEdges :: (Traversable f) => NodeId -> SymbolNode f c NodeId -> ParentMap -> ParentMap
processEdges a sn par = snFoldEdges par sn (\pm (Edge _ n) -> ILMM.insert n a pm)

-- private
node' :: (Traversable f, NodeC f c s m) => NodeId -> Node f c NodeId NodeId -> m ()
node' a b = do
  modifyML nodeStL $ \(NodeSt nx nm par) ->
    let par' = case b of
          NodeSymbol sn -> processEdges a sn par
          _ -> par
        nm' = ILM.insert a b nm
    in  pure (NodeSt nx nm' par')

-- private
fresh :: (NodeC f c s m) => m NodeId
fresh = stateML nodeStL (\ns -> let nx = ns.nsNext in pure (nx, ns {nsNext = succ nx}))

node :: (Traversable f, NodeC f c s m) => Node f c NodeId NodeId -> m NodeId
node b = do
  a <- fresh
  node' a b
  pure a

recursive :: (Traversable f, NodeC f c s m) => (m NodeId -> m (Node f c NodeId NodeId)) -> m NodeId
recursive f = do
  a <- fresh
  b <- f (fresh >>= \c -> c <$ node' c (NodeClone a))
  node' a b
  pure a

tree :: (Recursive t, Base t ~ f, Traversable f, NodeC f c s m) => t -> m NodeId
tree t = do
  fn <- traverse tree (project t)
  node (NodeSymbol (mkSymbolNode Empty (fmap (Edge Nothing) fn)))

-- -- reachable :: NodeId -> NodeMap f c -> [NodeId]
-- -- reachable a0 nm = go Empty a0 where
-- --   go a = undefined
--
-- data UnifyErr = UnifyErrArityMismatch !Int !Int
--   deriving stock (Eq, Ord, Show)
--
-- instance Exception UnifyErr
--
-- -- type ChildMap = Map Seg NodeId
-- --
-- -- type LabelMap = IntLikeMap ChildIx Label
-- --
-- -- data NodeInfo = NodeInfo
-- --   { niSize :: !Int
-- --   , niChildren :: !ChildMap
-- --   , niLabels :: !LabelMap
-- --   } deriving stock (Eq, Ord, Show)
--
-- unifyInfo :: NodeInfo -> NodeInfo -> Either UnifyErr NodeInfo
-- unifyInfo (NodeInfo sz1 chi1 lab1) (NodeInfo sz2 chi2 lab2) = do
--   unless (sz1 == sz2) (Left (UnifyErrArityMismatch sz1 sz2))
--   undefined
--
-- unify :: Traversable f => (NodeId -> NodeId -> m NodeId) -> NodeInfo -> f Edge -> NodeInfo -> f Edge -> m (Either UnifyErr (NodeInfo, f Edge))
-- unify g ni1 f1 ni2 f2 = error "TODO"
