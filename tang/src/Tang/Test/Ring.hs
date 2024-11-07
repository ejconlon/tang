{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Ring where

import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Tang.Dot (renderEqCon, renderNodeGraph)
import Tang.Ecta (NodeGraph, NodeId, SegEqCon)
import Tang.Render (RenderM)

data RingF r
  = RingZero
  | RingOne
  | RingAdd r r
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

renderRing :: RingF a -> Builder
renderRing = \case
  RingZero -> "0"
  RingOne -> "1"
  RingAdd _ _ -> "+"
  RingMul _ _ -> "*"
  RingVar v -> TLB.fromString v

renderRingGraph :: NodeId -> NodeGraph RingF SegEqCon -> RenderM ()
renderRingGraph = renderNodeGraph renderRing renderEqCon
