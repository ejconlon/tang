{-# LANGUAGE TemplateHaskell #-}

module Tang.Exp where

import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.String (IsString (..))

data Exp
  = ExpVar !String
  | ExpBool !Bool
  | ExpEq Exp Exp
  | ExpNot Exp
  | ExpIte Exp Exp Exp
  | ExpIff Exp Exp
  | ExpImplies Exp Exp
  | ExpXor Exp Exp
  | ExpAnd ![Exp]
  | ExpOr ![Exp]
  | ExpDistinct ![Exp]
  deriving stock (Eq, Ord, Show)

instance IsString Exp where
  fromString = ExpVar

makeBaseFunctor ''Exp
