{-# LANGUAGE TemplateHaskell #-}

module Tang.PropDef
  ( SProp (..)
  , SPropF (..)
  , DProp (..)
  , DPropF (..)
  , NProp (..)
  , NPropF (..)
  , Complement (..)
  , Polarity (..)
  , flipPol
  , negPol
  , polBool
  , Var (..)
  , posVar
  , negVar
  , flipVar
  , varBool
  , Clause (..)
  , clauseIsTriviallyFalse
  , Conjunction (..)
  , conjUpdate
  , conjIsTriviallyTrue
  , conjIsTriviallyFalse
  , VarConjunction (..)
  , varConjUpdate
  , varConjIsTriviallyTrue
  , varConjIsTriviallyFalse
  , Assignment (..)
  , newAssignment
  )
where

import Data.Foldable (foldl')
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.String (IsString (..))
import GHC.Generics (Generic)

data SProp v
  = SPropVar !v
  | SPropBool !Bool
  | SPropNot (SProp v)
  | SPropAnd !(Seq (SProp v))
  | SPropOr !(Seq (SProp v))
  | SPropIf !(Seq (SProp v)) (SProp v)
  | SPropIff (SProp v) (SProp v)
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)

instance (IsString v) => IsString (SProp v) where
  fromString = SPropVar . fromString

makeBaseFunctor ''SProp

deriving stock instance (Eq v, Eq a) => (Eq (SPropF v a))

deriving stock instance (Show v, Show a) => (Show (SPropF v a))

deriving stock instance Generic (SPropF v a)

data DProp v
  = DPropVar !v
  | DPropBool !Bool
  | DPropNot (DProp v)
  | DPropAnd (DProp v) (DProp v)
  | DPropOr (DProp v) (DProp v)
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)

instance (IsString v) => IsString (DProp v) where
  fromString = DPropVar . fromString

makeBaseFunctor ''DProp

deriving stock instance (Eq v, Eq a) => (Eq (DPropF v a))

deriving stock instance (Show v, Show a) => (Show (DPropF v a))

deriving stock instance Generic (DPropF v a)

class (Eq b) => Complement b where
  complement :: b -> b

data Polarity = PolarityPos | PolarityNeg
  deriving stock (Eq, Ord, Show, Generic)

instance Complement Polarity where
  complement = flipPol

flipPol :: Polarity -> Polarity
flipPol = \case
  PolarityPos -> PolarityNeg
  PolarityNeg -> PolarityPos

negPol :: Polarity -> Bool -> Bool
negPol pol val =
  case pol of
    PolarityPos -> val
    PolarityNeg -> not val

polBool :: Polarity -> Bool
polBool = \case
  PolarityPos -> True
  PolarityNeg -> False

data Var v = Var
  { varPolarity :: !Polarity
  , varName :: !v
  }
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance (Eq v) => Complement (Var v) where
  complement = flipVar

posVar :: v -> Var v
posVar = Var PolarityPos

negVar :: v -> Var v
negVar = Var PolarityNeg

flipVar :: Var v -> Var v
flipVar (Var pol nm) = Var (flipPol pol) nm

varBool :: Var v -> Bool
varBool = polBool . varPolarity

data NProp v
  = NPropVar !v
  | NPropBool !Bool
  | NPropAnd (NProp v) (NProp v)
  | NPropOr (NProp v) (NProp v)
  deriving stock (Eq, Show, Generic, Functor, Foldable, Traversable)

makeBaseFunctor ''NProp

deriving stock instance (Eq v, Eq a) => (Eq (NPropF v a))

deriving stock instance (Show v, Show a) => (Show (NPropF v a))

deriving stock instance Generic (NPropF v a)

newtype Clause v = Clause {unClause :: Seq v}
  deriving newtype (Eq, Ord, Functor, Foldable, Semigroup, Monoid)
  deriving stock (Show)

instance Traversable Clause where
  traverse f = fmap Clause . traverse f . unClause

clauseIsTriviallyFalse :: Clause v -> Bool
clauseIsTriviallyFalse = Seq.null . unClause

newtype Conjunction v = Conjunction {unConjunction :: Seq (Clause v)}
  deriving newtype (Eq, Ord, Semigroup, Monoid)
  deriving stock (Show)

instance Functor Conjunction where
  fmap f = Conjunction . fmap (fmap f) . unConjunction

instance Foldable Conjunction where
  foldr f b = foldr (flip (foldr f)) b . unConjunction

instance Traversable Conjunction where
  traverse f = fmap Conjunction . traverse (traverse f) . unConjunction

conjUpdate :: (Complement v) => v -> Conjunction v -> Conjunction v
conjUpdate v (Conjunction cs) = Conjunction (cs >>= onClause)
 where
  onClause (Clause xs) =
    case Seq.elemIndexL v xs of
      Just _ -> Seq.empty
      Nothing ->
        let c = complement v
        in  Seq.singleton (Clause (Seq.filter (/= c) xs))

conjIsTriviallyTrue :: Conjunction v -> Bool
conjIsTriviallyTrue = Seq.null . unConjunction

conjIsTriviallyFalse :: Conjunction v -> Bool
conjIsTriviallyFalse = any clauseIsTriviallyFalse . unConjunction

newtype VarConjunction v = VarConjunction {unVarConjunction :: Conjunction (Var v)}
  deriving newtype (Eq, Ord, Semigroup, Monoid)
  deriving stock (Show)

varConjUpdate :: (Eq v) => Var v -> VarConjunction v -> VarConjunction v
varConjUpdate v = VarConjunction . conjUpdate v . unVarConjunction

varConjIsTriviallyTrue :: VarConjunction v -> Bool
varConjIsTriviallyTrue = conjIsTriviallyTrue . unVarConjunction

varConjIsTriviallyFalse :: VarConjunction v -> Bool
varConjIsTriviallyFalse = conjIsTriviallyFalse . unVarConjunction

newtype Assignment v = Assignment {unAssignment :: Map v Bool}
  deriving newtype (Eq, Semigroup, Monoid)
  deriving stock (Show)

newAssignment :: (Ord v) => (Foldable f) => f (Var v) -> Assignment v
newAssignment = Assignment . foldl' go Map.empty
 where
  go m (Var pol nm) = Map.insert nm (polBool pol) m
