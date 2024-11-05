{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Symbolic where

import Data.Sequence (Seq)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Tang.Dot (renderCon, renderNodeGraph)
import Tang.Ecta (Con, Edge (..), GraphM, NodeGraph, NodeId, addSymbol)
import Tang.Render (RenderM)

newtype Symbol = Symbol {unSymbol :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

exampleX :: GraphM Symbolic Con NodeId
exampleX = addSymbol [] (Symbolic "x" [])

exampleFxx :: GraphM Symbolic Con NodeId
exampleFxx = do
  ex <- fmap (Edge Nothing) exampleX
  addSymbol [] (Symbolic "f" [ex, ex])

renderSymbolic :: Symbolic a -> Builder
renderSymbolic (Symbolic (Symbol s) _) = TLB.fromText s

renderSymbolicGraph :: NodeId -> NodeGraph Symbolic Con -> RenderM ()
renderSymbolicGraph = renderNodeGraph renderSymbolic renderCon
