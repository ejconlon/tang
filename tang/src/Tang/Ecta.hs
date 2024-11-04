{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Monad.State.Strict (MonadState, State, runState)
import Data.Foldable (toList)
import Data.Functor.Foldable (Base, Recursive (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Data.String (IsString)
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.MultiMap (IntLikeMultiMap)
import IntLike.MultiMap qualified as ILMM
import IntLike.Set (IntLikeSet)
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

data Edge = Edge !(Maybe Label) !NodeId
  deriving stock (Eq, Ord, Show)

data SymbolNode f c = SymbolNode !(Seq c) !(f Edge)

deriving stock instance (Eq c, Eq (f Edge)) => Eq (SymbolNode f c)

deriving stock instance (Ord c, Ord (f Edge)) => Ord (SymbolNode f c)

deriving stock instance (Show c, Show (f Edge)) => Show (SymbolNode f c)

snConTrav :: Traversal (SymbolNode f c) (SymbolNode f d) c d
snConTrav = traversalVL (\g (SymbolNode cs fe) -> fmap (`SymbolNode` fe) (traverse g cs))

snSymTrans :: NatTrans f g -> SymbolNode f c -> SymbolNode g c
snSymTrans nt (SymbolNode cs fe) = SymbolNode cs (runNatTrans nt fe)

snEdgeTrav :: (Traversable f) => Traversal' (SymbolNode f c) Edge
snEdgeTrav = traversalVL (\g (SymbolNode cs fe) -> fmap (SymbolNode cs) (traverse g fe))

snFoldEdges :: (Traversable f) => b -> SymbolNode f c -> (b -> Edge -> b) -> b
snFoldEdges b sn f = foldlOf' snEdgeTrav f b sn

data Node f c
  = NodeSymbol !(SymbolNode f c)
  | NodeChoice !(IntLikeSet NodeId)
  | NodeClone !NodeId

deriving stock instance (Eq c, Eq (f Edge)) => Eq (Node f c)

deriving stock instance (Ord c, Ord (f Edge)) => Ord (Node f c)

deriving stock instance (Show c, Show (f Edge)) => Show (Node f c)

nodeConTrav :: Traversal (Node f c) (Node f d) c d
nodeConTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> fmap NodeSymbol (traverseOf snConTrav g sn)
  NodeChoice xs -> pure (NodeChoice xs)
  NodeClone n -> pure (NodeClone n)

nodeSymTrans :: NatTrans f g -> Node f c -> Node g c
nodeSymTrans nt = \case
  NodeSymbol sn -> NodeSymbol (snSymTrans nt sn)
  NodeChoice xs -> NodeChoice xs
  NodeClone n -> NodeClone n

choice :: (Foldable g) => g NodeId -> Node f c
choice = NodeChoice . ILS.fromList . toList

type ChildMap = Map Seg NodeId

type LabelMap = IntLikeMap ChildIx Label

data NodeInfo f c = NodeInfo
  { niSize :: !Int
  , niChildren :: !ChildMap
  , niLabels :: !LabelMap
  , niNode :: !(Node f c)
  }

deriving stock instance (Eq c, Eq (f Edge)) => Eq (NodeInfo f c)

deriving stock instance (Show c, Show (f Edge)) => Show (NodeInfo f c)

type NodeMap f c = IntLikeMap NodeId (NodeInfo f c)

type ParentMap = IntLikeMultiMap NodeId NodeId

data NodeGraph f c = NodeGraph
  { ngRoot :: !NodeId
  , ngNodes :: !(NodeMap f c)
  , ngParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f Edge)) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f Edge)) => Show (NodeGraph f c)

data NodeSt f c = NodeSt
  { nsNext :: !NodeId
  , nsNodes :: !(NodeMap f c)
  , nsParents :: !ParentMap
  }

deriving stock instance (Eq c, Eq (f Edge)) => Eq (NodeSt f c)

deriving stock instance (Show c, Show (f Edge)) => Show (NodeSt f c)

type NodeM f c = State (NodeSt f c)

class HasNodeSt f c s | s -> f c where
  nodeStL :: Lens' s (NodeSt f c)

instance HasNodeSt f c (NodeSt f c) where
  nodeStL = equality'

type NodeC f c s m = (HasNodeSt f c s, MonadState s m)

build :: NodeM f c NodeId -> NodeGraph f c
build m =
  let (r, NodeSt _ nm par) = runState m (NodeSt 0 ILM.empty ILM.empty)
  in  NodeGraph r nm par

-- private
processEdges :: (Traversable f) => NodeId -> SymbolNode f c -> ParentMap -> (Int, ChildMap, LabelMap, ParentMap)
processEdges a sn par = snFoldEdges (0, Map.empty, ILM.empty, par) sn $ \(i, cm, lm, pm) (Edge ml n) ->
  let i' = succ i
      cm' = Map.insert (SegIndex (ChildIx i)) n cm
      (cm'', lm') = maybe (cm', lm) (\l -> (Map.insert (SegLabel l) n cm', ILM.insert (ChildIx i) l lm)) ml
      pm' = ILMM.insert n a pm
  in  (i', cm'', lm', pm')

-- private
node' :: (Traversable f, NodeC f c s m) => NodeId -> Node f c -> m ()
node' a b = do
  modifyML nodeStL $ \(NodeSt nx nm par0) ->
    let (sz2, chi2, lab2, par2) = case b of
          NodeSymbol sn -> processEdges a sn par0
          _ -> (0, Map.empty, ILM.empty, par0)
        nm' = ILM.insert a (NodeInfo sz2 chi2 lab2 b) nm
    in  pure (NodeSt nx nm' par2)

-- private
fresh :: (NodeC f c s m) => m NodeId
fresh = stateML nodeStL (\ns -> let nx = ns.nsNext in pure (nx, ns {nsNext = succ nx}))

node :: (Traversable f, NodeC f c s m) => Node f c -> m NodeId
node b = do
  a <- fresh
  node' a b
  pure a

recursive :: (Traversable f, NodeC f c s m) => (NodeId -> m (Node f c)) -> m NodeId
recursive f = do
  a <- fresh
  b <- f a
  node' a b
  pure a

tree :: (Recursive t, Base t ~ f, Traversable f, NodeC f c s m) => t -> m NodeId
tree t = do
  fn <- traverse tree (project t)
  node (NodeSymbol (SymbolNode Empty (fmap (Edge Nothing) fn)))
