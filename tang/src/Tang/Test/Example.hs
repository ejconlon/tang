{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Example where

import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))
import Data.Sequence (Seq)
import Tang.Ecta

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

exampleX :: NodeMap Symbolic (Con Path)
exampleX = ngNodes $ build $ do
  node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))

exampleFxx :: NodeMap Symbolic (Con Path)
exampleFxx = ngNodes $ build $ do
  ex <- Edge Nothing <$> node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))
  node (NodeSymbol (SymbolNode [] (Symbolic "f" [ex, ex])))

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

data RingRel = RingRelEq !Ring !Ring
  deriving stock (Eq, Ord, Show)
