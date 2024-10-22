{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Tang.Ecta where

import Control.Exception (Exception)
import Control.Monad (unless)
import Control.Monad.Except (Except, MonadError (..), runExcept)
import Control.Monad.Reader (MonadReader (..), ReaderT, asks, runReaderT)
import Control.Monad.State (MonadState (..), State, StateT, execStateT, gets, modify', runState)
import Data.Foldable (for_, toList, traverse_)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.String (IsString)
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import Optics (Traversal, traversalVL, traverseOf)

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

data Edge r = Edge !(Maybe Label) !r
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

data SymbolNode f c r = SymbolNode !(Seq c) !(f (Edge r))
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq r, Eq (f (Edge r))) => Eq (SymbolNode f c r)

deriving stock instance (Ord c, Ord r, Ord (f (Edge r))) => Ord (SymbolNode f c r)

deriving stock instance (Show c, Show r, Show (f (Edge r))) => Show (SymbolNode f c r)

snConTrav :: Traversal (SymbolNode f c r) (SymbolNode f d r) c d
snConTrav = traversalVL (\g (SymbolNode cs fe) -> fmap (`SymbolNode` fe) (traverse g cs))

snSymTrans :: NatTrans f g -> SymbolNode f c r -> SymbolNode g c r
snSymTrans nt (SymbolNode cs fe) = SymbolNode cs (runNatTrans nt fe)

data NodeF f c r
  = NodeSymbol !(SymbolNode f c r)
  | NodeChoice !(Seq r)
  | NodeClone !NodeId
  deriving stock (Functor, Foldable, Traversable)

deriving stock instance (Eq c, Eq r, Eq (f (Edge r))) => Eq (NodeF f c r)

deriving stock instance (Ord c, Ord r, Ord (f (Edge r))) => Ord (NodeF f c r)

deriving stock instance (Show c, Show r, Show (f (Edge r))) => Show (NodeF f c r)

nfConTrav :: Traversal (NodeF f c r) (NodeF f d r) c d
nfConTrav = traversalVL $ \g -> \case
  NodeSymbol sn -> fmap NodeSymbol (traverseOf snConTrav g sn)
  NodeChoice xs -> pure (NodeChoice xs)
  NodeClone n -> pure (NodeClone n)

nfSymTrans :: NatTrans f g -> NodeF f c r -> NodeF g c r
nfSymTrans = undefined

type NodeMap f c i = IntLikeMap i (NodeF f c i)

type InitNodeMap f c = NodeMap f c NodeId

data NodeGraph f c = NodeGraph
  { ngRoot :: !NodeId
  , ngMap :: !(InitNodeMap f c)
  }

deriving stock instance (Eq c, Eq (f (Edge NodeId))) => Eq (NodeGraph f c)

deriving stock instance (Show c, Show (f (Edge NodeId))) => Show (NodeGraph f c)

data NodeSt f c = NodeSt
  { nsNext :: !NodeId
  , nsMap :: !(InitNodeMap f c)
  }

deriving stock instance (Eq c, Eq (f (Edge NodeId))) => Eq (NodeSt f c)

deriving stock instance (Show c, Show (f (Edge NodeId))) => Show (NodeSt f c)

type NodeM f c = State (NodeSt f c)

build :: NodeM f c NodeId -> NodeGraph f c
build m =
  let (r, NodeSt _ nm) = runState m (NodeSt 0 ILM.empty)
  in  NodeGraph r nm

-- TODO actually traverse and re-unique NodeIds, introducing equalities instead
node :: NodeF f c NodeId -> NodeM f c NodeId
node x = state (\(NodeSt ni nm) -> (ni, NodeSt (succ ni) (ILM.insert ni x nm)))

data ResErr = ResErrMissing !NodeId
  deriving stock (Eq, Ord, Show)

instance Exception ResErr

data ResPath = ResPath !ChoiceId !Path
  deriving stock (Eq, Ord, Show)

isFullyResolved :: ResPath -> Bool
isFullyResolved (ResPath _ p) = Seq.null p

type ResNodeMap f d = NodeMap f d ChoiceId

type ChoiceMap = IntLikeMap ChoiceId NodeId

data Resolution f d = Resolution
  { resChoiceMap :: !ChoiceMap
  , resNodeMap :: !(ResNodeMap f d)
  }

deriving stock instance (Eq d, Eq (f (Edge ChoiceId))) => Eq (Resolution f d)

deriving stock instance (Show d, Show (f (Edge ChoiceId))) => Show (Resolution f d)

data ResEnv f c = ResEnv
  { rePath :: !Path
  , reInitMap :: !(InitNodeMap f c)
  }

newResEnv :: InitNodeMap f c -> ResEnv f c
newResEnv = ResEnv Empty

data ResSt f d = ResSt
  { rsNext :: !ChoiceId
  , rsSeen :: !(IntLikeSet NodeId)
  , rsChoiceMap :: !ChoiceMap
  , rsNodeMap :: !(ResNodeMap f d)
  }

deriving stock instance (Eq d, Eq (f (Edge ChoiceId))) => Eq (ResSt f d)

deriving stock instance (Show d, Show (f (Edge ChoiceId))) => Show (ResSt f d)

newResSt :: ResSt f d
newResSt = ResSt 0 ILS.empty ILM.empty ILM.empty

type ResM f c d = ReaderT (ResEnv f c) (StateT (ResSt f d) (Except ResErr))

execResM :: ResM f c d () -> InitNodeMap f c -> Either ResErr (Resolution f d)
execResM m nm =
  fmap
    (\rs -> Resolution rs.rsChoiceMap rs.rsNodeMap)
    (runExcept (execStateT (runReaderT m (newResEnv nm)) newResSt))

resolve :: (Traversable f, Traversable g) => InitNodeMap f (g Path) -> Either ResErr (Resolution f (g ResPath))
resolve nm0 = execResM (traverse_ (uncurry go1) (ILM.toList nm0)) nm0
 where
  go1 n nf = do
    seen <- gets (\rs -> ILS.member n rs.rsSeen)
    unless seen $ do
      modify' (\rs -> rs {rsSeen = ILS.insert n rs.rsSeen})
      nm <- asks reInitMap
      case nf of
        NodeSymbol (SymbolNode _cs fe) -> do
          for_ fe $ \(Edge _ml n') -> do
            case ILM.lookup n' nm of
              Nothing -> throwError (ResErrMissing n')
              Just nf' -> go1 n' nf'
            error "TODO"
        _ -> error "TODO"

-- NodeChoice xs -> do
--   nm <- asks reInitMap
--   for_ xs $ \x ->
--
--     case ILM.lookup x nm of
-- NodeClone _ -> undefined
-- _ <- pure (rs.rsChoiceMap)

-- go1 _ _ = modify' $ \(ResSt c m) ->
--   let x =  error "TODO"
--   in ResSt (succ c) (ILM.insert c x m)

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

exampleX :: InitNodeMap Symbolic (Con Path)
exampleX = ngMap $ build $ do
  node (NodeSymbol (SymbolNode Empty (Symbolic "x" Empty)))

exampleFxx :: InitNodeMap Symbolic (Con Path)
exampleFxx = ngMap $ build $ do
  ex <- Edge Nothing <$> node (NodeSymbol (SymbolNode Empty (Symbolic "x" Empty)))
  node (NodeSymbol (SymbolNode Empty (Symbolic "f" [ex, ex])))

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList
