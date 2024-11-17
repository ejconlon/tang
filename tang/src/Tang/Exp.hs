{-# LANGUAGE TemplateHaskell #-}

module Tang.Exp where

import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.String (IsString (..))

data Ty
  = TyVar !String
  | TyBool
  | TyBv !Int
  deriving stock (Eq, Ord, Show)

instance IsString Ty where
  fromString = TyVar

makeBaseFunctor ''Ty

data Tm
  = TmVar !String
  | TmBool !Bool
  | TmInt !Ty !Int
  | TmEq Tm Tm
  | TmNot Tm
  | TmIte Tm Tm Tm
  | TmIff Tm Tm
  | TmImplies Tm Tm
  | TmXor Tm Tm
  | TmAnd ![Tm]
  | TmOr ![Tm]
  | TmDistinct ![Tm]
  | TmApp !String ![Tm]
  deriving stock (Eq, Ord, Show)

instance IsString Tm where
  fromString = TmVar

makeBaseFunctor ''Tm

tmBv :: Int -> Int -> Tm
tmBv = TmInt . TyBv

data TmDef = TmDef ![Ty] !Ty
  deriving stock (Eq, Ord, Show)

-- Nothing means uninterpreted
newtype TyDef = TyDef (Maybe Ty)
  deriving stock (Eq, Ord, Show)

-- data Def = DefTm !TmDef | DefTy !TyDef
--   deriving stock (Eq, Ord, Show)
