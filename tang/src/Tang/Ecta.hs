{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Exception (Exception)
import Control.Monad.Except (runExcept, throwError)
import Control.Monad.Identity (Identity)
import Control.Monad.State.Strict (StateT, modify', runState, state)
import Control.Placeholder (todo)
import Data.Foldable (toList)
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
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Traversal, Traversal', foldlOf', traversalVL, traverseOf)
import Tang.Search (SearchM, interleaveSeq)

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

type NodeT f c = StateT (NodeSt f c)

type NodeM f c = NodeT f c Identity

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
node' :: (Traversable f) => NodeId -> Node f c -> NodeM f c ()
node' a b = do
  modify' $ \(NodeSt nx nm par0) ->
    let (sz2, chi2, lab2, par2) = case b of
          NodeSymbol sn -> processEdges a sn par0
          _ -> (0, Map.empty, ILM.empty, par0)
        nm' = ILM.insert a (NodeInfo sz2 chi2 lab2 b) nm
    in  NodeSt nx nm' par2

-- private
fresh :: NodeM f c NodeId
fresh = state (\ns -> let nx = ns.nsNext in (nx, ns {nsNext = succ nx}))

node :: (Traversable f) => Node f c -> NodeM f c NodeId
node b = do
  a <- fresh
  node' a b
  pure a

recursive :: (Traversable f) => (NodeId -> NodeM f c (Node f c)) -> NodeM f c NodeId
recursive f = do
  a <- fresh
  b <- f a
  node' a b
  pure a

tree :: (Recursive t, Base t ~ f, Traversable f) => t -> NodeM f c NodeId
tree t = do
  fn <- traverse tree (project t)
  node (NodeSymbol (SymbolNode Empty (fmap (Edge Nothing) fn)))

data ResErr
  = ResErrSegMissing !Seg
  | ResErrNodeMissing !NodeId
  | ResErrPathChoice !NodeId
  deriving stock (Eq, Ord, Show)

instance Exception ResErr

data ResPath = ResPath !NodeId !Path
  deriving stock (Eq, Ord, Show)

isFullyResolved :: ResPath -> Bool
isFullyResolved (ResPath _ p) = Seq.null p

resolvePath :: NodeMap f c -> NodeId -> ChildMap -> Path -> Either ResErr ResPath
resolvePath nm = go
 where
  go a chi = \case
    Empty -> pure (ResPath a Empty)
    p :<| ps -> case Map.lookup p chi of
      Nothing -> throwError (ResErrSegMissing p)
      Just a' -> case ILM.lookup a' nm of
        Nothing -> throwError (ResErrNodeMissing a')
        Just (NodeInfo _ chi' _ b') ->
          case b' of
            NodeChoice _ -> throwError (ResErrPathChoice a')
            NodeClone _ -> pure (ResPath a' ps)
            NodeSymbol _ -> go a' chi' ps

resolveAll :: (Traversable g) => NodeMap f (g Path) -> Either ResErr (NodeMap f (g ResPath))
resolveAll nm0 = fmap ILM.fromList (runExcept (traverse (uncurry goRoot) (ILM.toList nm0)))
 where
  goRoot a (NodeInfo sz chi lab b) = do
    b' <- case b of
      NodeChoice ns -> pure (NodeChoice ns)
      NodeClone n -> pure (NodeClone n)
      NodeSymbol (SymbolNode cs fe) -> do
        cs' <- traverse (traverse (goRes a chi)) cs
        pure (NodeSymbol (SymbolNode cs' fe))
    pure (a, NodeInfo sz chi lab b')
  goRes a chi = either throwError pure . resolvePath nm0 a chi

newtype Fix f = Fix {unFix :: f (Fix f)}

deriving stock instance (Eq (f (Fix f))) => Eq (Fix f)

deriving stock instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

type EnumSt = ()

type EnumM = SearchM ResErr EnumSt

enumerate :: (Traversable f) => NodeGraph f (Con ResPath) -> EnumM (Fix f)
enumerate (NodeGraph r nm _) = go r
 where
  go a = case ILM.lookup a nm of
    Nothing -> throwError (ResErrNodeMissing a)
    Just (NodeInfo _ _ _ b) -> case b of
      NodeSymbol _ -> todo
      NodeChoice ns -> interleaveSeq (Seq.fromList (fmap go (ILS.toList ns)))
      NodeClone _ -> todo
