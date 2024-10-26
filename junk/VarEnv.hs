module Tang.VarEnv
  ( VarId (..)
  , VarType (..)
  , VarEnv (..)
  , empty
  , lookupFwd
  , lookupBwd
  , addNamed
  , addUnnamed
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM

newtype VarId = VarId {unVarId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum)

data VarType v
  = VarTypeNamed !v
  | VarTypeUnnamed
  deriving stock (Eq, Show, Generic)

data VarEnv v = VarEnv
  { veNext :: !VarId
  , veFwd :: !(IntLikeMap VarId (VarType v))
  , veBwd :: !(Map v VarId)
  }
  deriving stock (Eq, Show)

empty :: VarEnv v
empty = VarEnv (VarId 0) ILM.empty Map.empty

lookupFwd :: VarId -> VarEnv v -> Maybe (VarType v)
lookupFwd n = ILM.lookup n . veFwd

lookupBwd :: (Ord v) => v -> VarEnv v -> Maybe VarId
lookupBwd v = Map.lookup v . veBwd

addNamed :: (Ord v) => v -> VarEnv v -> (VarId, VarEnv v)
addNamed v ve@(VarEnv n f b) =
  case Map.lookup v b of
    Nothing -> (n, VarEnv (succ n) (ILM.insert n (VarTypeNamed v) f) (Map.insert v n b))
    Just x -> (x, ve)

addUnnamed :: VarEnv v -> (VarId, VarEnv v)
addUnnamed (VarEnv n f b) = (n, VarEnv (succ n) (ILM.insert n VarTypeUnnamed f) b)
