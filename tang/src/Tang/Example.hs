{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Example where

import Data.Sequence (Seq)
import Tang.Ecta2

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

exampleX :: NodeMap Symbolic (Con Path)
exampleX = ngNodes $ build $ do
  node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))

exampleFxx :: NodeMap Symbolic (Con Path)
exampleFxx = ngNodes $ build $ do
  ex <- Edge Nothing <$> node (NodeSymbol (SymbolNode [] (Symbolic "x" [])))
  node (NodeSymbol (SymbolNode [] (Symbolic "f" [ex, ex])))
