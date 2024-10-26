{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Symbolic where

import Data.Sequence (Seq)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Tang.Dot (renderCon, renderNodeGraph)
import Tang.Ecta
  ( Con
  , Edge (..)
  , Node (..)
  , NodeGraph
  , Path
  , Symbol (..)
  , SymbolNode (..)
  , build
  , node
  )
import Tang.Render (RenderM)

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type SymbolicNodeGraph = NodeGraph Symbolic (Con Path)

exampleX :: SymbolicNodeGraph
exampleX = build $ do
  node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))

exampleFxx :: SymbolicNodeGraph
exampleFxx = build $ do
  ex <- Edge Nothing <$> node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))
  node (NodeSymbol (SymbolNode [] (Symbolic "f" [ex, ex])))

renderSymbolic :: Symbolic a -> Builder
renderSymbolic (Symbolic (Symbol s) _) = TLB.fromText s

renderSymbolicGraph :: SymbolicNodeGraph -> RenderM ()
renderSymbolicGraph = renderNodeGraph renderSymbolic renderCon
