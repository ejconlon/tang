module Tang.Ecta where

import Control.Exception (Exception)
import Control.Monad.State (MonadState (..), State, runState)
import Control.Monad.Reader (MonadReader (..), ReaderT, runReaderT)
import Control.Monad.Except (MonadError (..), ExceptT, runExceptT)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.String (IsString)
import Data.Text (Text)
import Data.Bifunctor (Bifunctor (..))
import Data.Bifoldable (Bifoldable (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Foldable (Base, Recursive (..), Corecursive (..))
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM

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

data Labeled r = Labeled !(Maybe Label) !r
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

data SymbolNode c r = SymbolNode !Symbol !(Seq (Labeled r)) !(Seq c)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Bifunctor SymbolNode where
  bimap f g (SymbolNode s xs cs) = SymbolNode s (fmap (fmap g) xs) (fmap f cs)

instance Bifoldable SymbolNode where
  bifoldr f g z (SymbolNode _ xs cs) = foldr (\(Labeled _ r) -> g r) (foldr f z cs) xs

instance Bitraversable SymbolNode where
  bitraverse f g (SymbolNode s xs cs) = liftA2 (SymbolNode s) (traverse (traverse g) xs) (traverse f cs)

newtype ChoiceNode r = ChoiceNode (Labeled (Seq r))
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

data NodeF c r
  = NodeSymbol !(SymbolNode c r)
  | NodeChoice !(ChoiceNode r)
  | NodeClone !NodeId
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Bifunctor NodeF where
  bimap f g = \case
    NodeSymbol x -> NodeSymbol (bimap f g x)
    NodeChoice x -> NodeChoice (fmap g x)
    NodeClone x -> NodeClone x

instance Bifoldable NodeF where
  bifoldr f g z = \case
    NodeSymbol x -> bifoldr f g z x
    NodeChoice x -> foldr g z x
    NodeClone _ -> z

instance Bitraversable NodeF where
  bitraverse f g = \case
    NodeSymbol x -> fmap NodeSymbol (bitraverse f g x)
    NodeChoice x -> fmap NodeChoice (traverse g x)
    NodeClone x -> pure (NodeClone x)

newtype Node c = Node {unNode :: NodeF c (Node c)}
  deriving stock (Eq, Ord, Show)

type instance Base (Node c) = NodeF c

instance Recursive (Node c) where
  project = unNode

instance Corecursive (Node c) where
  embed = Node

type NodeMap i c j = IntLikeMap i (NodeF c j)

type InitNodeMap c = NodeMap NodeId c NodeId

data NodeGraph c = NodeGraph
  { ngRoot :: !NodeId
  , ngMap :: !(InitNodeMap c)
  }
  deriving stock (Eq, Show)

data NodeSt c = NodeSt
  { nsNext :: !NodeId
  , nsMap :: !(InitNodeMap c)
  }
  deriving stock (Eq, Show)

type NodeM c = State (NodeSt c)

build :: NodeM c NodeId -> NodeGraph c
build m =
  let (r, NodeSt _ nm) = runState m (NodeSt 0 mempty)
  in  NodeGraph r nm

node :: NodeF c NodeId -> NodeM c NodeId
node x = state (\(NodeSt ni nm) -> (ni, NodeSt (succ ni) (ILM.insert ni x nm)))

data ConvertErr
  deriving stock (Eq, Ord, Show)

instance Exception ConvertErr

data ResPath = ResPath !ChoiceId !Path
  deriving stock (Eq, Ord, Show)

isFullyResolved :: ResPath -> Bool
isFullyResolved (ResPath _ p) = Seq.null p

data Choice = Choice !ChoiceId !NodeId
  deriving stock (Eq, Ord, Show)

type ResNodeMap d = NodeMap ChoiceId d Choice

type ResEnv c = InitNodeMap c

data ResSt d = ResSt
  { rsNext :: !ChoiceId
  , rsMap :: !(ResNodeMap d)
  }

type ResM c d = ReaderT (ResEnv c) (ExceptT ConvertErr (State (ResSt d)))

resolve :: (Traversable g) => InitNodeMap (g Path) -> Either ConvertErr (ResNodeMap (g ResPath))
resolve nm =  undefined

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList

traverseFirst :: (Bitraversable f, Applicative m) => (a -> m x) -> f a b -> m (f x b)
traverseFirst = flip bitraverse pure

traverseSecond :: (Bitraversable f, Applicative m) => (b -> m y) -> f a b -> m (f a y)
traverseSecond = bitraverse pure
