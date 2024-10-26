module Tang.Test.Ring where

import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))

data RingF r
  = RingZero
  | RingOne
  | RingPlus r r
  | RingMul r r
  | RingVar !String
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

newtype Ring = Ring {unRing :: RingF Ring}
  deriving stock (Eq, Ord, Show)

type instance Base Ring = RingF

instance Recursive Ring where
  project = unRing

instance Corecursive Ring where
  embed = Ring

data Rel = RelEq !Ring !Ring
  deriving stock (Eq, Ord, Show)
