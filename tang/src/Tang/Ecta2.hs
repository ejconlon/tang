{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta2 where

import Control.Exception (Exception)
import Control.Monad (void)
import Control.Monad.Except (Except, MonadError (..), runExcept)
import Control.Monad.Reader (MonadReader (..), ReaderT, asks, runReaderT)
import Control.Monad.State (MonadState (..), State, StateT, execStateT, gets, modify', runState)
import Data.Foldable (for_, traverse_, toList)
import Data.Traversable (for)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.String (IsString)
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Traversal, traversalVL, traverseOf, Traversal', foldlOf')
import Data.Functor.Foldable (Recursive (..), Base)
import Tang.Util (foldM')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import IntLike.MultiMap qualified as ILMM
import IntLike.MultiMap (IntLikeMultiMap)

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

newtype ChoiceId = ChoiceId {unChoiceId :: Int}
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

snEdgeTrav :: Traversable f => Traversal' (SymbolNode f c) Edge
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

type NodeMap f c = IntLikeMap NodeId (Node f c)
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

build :: NodeM f c NodeId -> NodeGraph f c
build m =
  let (r, NodeSt _ nm par) = runState m (NodeSt 0 ILM.empty ILM.empty)
  in  NodeGraph r nm par

-- private
node' :: (Traversable f) => NodeId -> Node f c -> NodeM f c ()
node' a b = do
  modify' $ \(NodeSt ni nm par) ->
    let nm' = ILM.insert a b nm
        par' = case b of
              NodeSymbol sn -> snFoldEdges par sn (\p (Edge _ n) -> ILMM.insert n ni p)
              _ -> par
    in NodeSt ni nm' par'

node :: (Traversable f) => Node f c -> NodeM f c NodeId
node b = do
  a <- state (\ns -> let ni = ns.nsNext in (ni, ns { nsNext = succ ni }))
  node' a b
  pure a

recursive :: (Traversable f) => (NodeId -> NodeM f c (Node f c)) -> NodeM f c NodeId
recursive f = do
  a <- state (\ns -> let ni = ns.nsNext in (ni, ns { nsNext = succ ni }))
  b <- f a
  node' a b
  pure a

tree :: (Recursive t, Base t ~ f, Traversable f) => t -> NodeM f c NodeId
tree t = do
  fn <- traverse tree (project t)
  node (NodeSymbol (SymbolNode Empty (fmap (Edge Nothing) fn)))

