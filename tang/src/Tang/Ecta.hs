module Tang.Ecta where

import Control.Monad.State (MonadState (..), State, runState)
import Data.Foldable (toList)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.String (IsString)
import Data.Text (Text)

newtype Sym = Sym {unSym :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

newtype Label = Label {unLabel :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

newtype Index = Index {unIndex :: Int}
  deriving newtype (Eq, Ord, Num, Enum)
  deriving stock (Show)

newtype NodeId = NodeId {unNodeId :: Int}
  deriving newtype (Eq, Ord, Num, Enum)
  deriving stock (Show)

newtype ChoiceId = ChoiceId {unChoiceId :: Int}
  deriving newtype (Eq, Ord, Num, Enum)
  deriving stock (Show)

type Path = Seq Index

data Con = ConEq !Path !Path
  deriving stock (Eq, Ord, Show)

data NodeF r
  = NodeChoice !(Maybe Label) !(Seq r)
  | NodeSym !Sym !(Seq Con) !(Seq (Maybe Label, r))
  | NodeClone !r
  deriving stock (Eq, Ord, Show, Functor)

newtype Node = Node {unNode :: NodeF Node}
  deriving stock (Eq, Ord, Show)

type NodeMap = Map NodeId (NodeF NodeId)

data NodeGraph = NodeGraph
  { ngRoot :: !NodeId
  , ngMap :: !NodeMap
  }
  deriving stock (Eq, Show)

data St = St
  { stNext :: !NodeId
  , stMap :: !NodeMap
  }
  deriving stock (Eq, Show)

type NodeM = State St

build :: NodeM NodeId -> NodeGraph
build m =
  let (r, St _ nm) = runState m (St 0 mempty)
  in  NodeGraph r nm

node :: NodeF NodeId -> NodeM NodeId
node x = state (\(St ni nm) -> (ni, St (succ ni) (Map.insert ni x nm)))

seqFromFoldable :: (Foldable f) => f a -> Seq a
seqFromFoldable = Seq.fromList . toList
