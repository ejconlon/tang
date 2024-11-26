{-# LANGUAGE TemplateHaskell #-}

module Tang.Exp where

import Control.Monad ((>=>))
import Data.Coerce (Coercible, coerce)
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
  | TmLt Tm Tm
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

data Val
  = ValInt !Ty !Int
  | ValBool !Bool
  deriving stock (Eq, Ord, Show)

expVal :: Tm -> Maybe Val
expVal = \case
  TmBool b -> Just (ValBool b)
  TmInt ty i -> Just (ValInt ty i)
  _ -> Nothing

valExp :: Val -> Tm
valExp = \case
  ValBool b -> TmBool b
  ValInt ty i -> TmInt ty i

data Conv x y = Conv
  { convTo :: !(x -> y)
  , convFrom :: !(y -> Maybe x)
  }

convId :: Conv x x
convId = Conv id Just

convCompose :: Conv y z -> Conv x y -> Conv x z
convCompose (Conv toYZ fromYZ) (Conv toXY fromXY) = Conv (toYZ . toXY) (fromYZ >=> fromXY)

convInt :: (Coercible x Int, Coercible y Int) => Conv x y
convInt = Conv coerce (Just . coerce)

convNull :: (Eq y) => y -> Conv x y -> Conv (Maybe x) y
convNull nl (Conv to from) =
  Conv
    (maybe nl to)
    (\y -> if y == nl then Nothing else Just (from y))

convTmVal :: Conv Val Tm
convTmVal = Conv valExp expVal
