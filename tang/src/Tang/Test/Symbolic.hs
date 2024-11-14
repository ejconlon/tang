{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Symbolic where

import Control.Monad.Identity (Identity (..))
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Prettyprinter (Doc, Pretty (..))
import Prettyprinter qualified as P
import Tang.Align (Alignable (..), EqAlignErr, eqAlignWithM)
import Tang.Dot (renderEqCon, renderNodeGraph)
import Tang.Ecta (Edge (..), EqCon (..), GraphM, NodeGraph, NodeId, Seg (..), SegEqCon, addSymbol, addUnion)
import Tang.Render (RenderM)

newtype Symbol = Symbol {unSymbol :: Text}
  deriving newtype (Eq, Ord, IsString)
  deriving stock (Show)

data Symbolic a = Symbolic !Symbol !(Seq a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

symPrettyM :: (Monad m) => (a -> m (Doc ann)) -> Symbolic a -> m (Doc ann)
symPrettyM f (Symbolic hd tl) =
  traverse f (toList tl) <&> \fs ->
    "(" <> P.hsep (pretty (unSymbol hd) : fs) <> ")"

symPretty :: (a -> Doc ann) -> Symbolic a -> Doc ann
symPretty f = runIdentity . symPrettyM (Identity . f)

instance (Pretty a) => Pretty (Symbolic a) where
  pretty = symPretty pretty

instance Alignable EqAlignErr Symbolic where
  alignWithM = eqAlignWithM

exampleX :: GraphM Symbolic SegEqCon NodeId
exampleX = addSymbol (Symbolic "x" []) Set.empty

exampleFxx :: GraphM Symbolic SegEqCon NodeId
exampleFxx = do
  ex <- fmap (Edge Nothing) exampleX
  addSymbol (Symbolic "f" [ex, ex]) Set.empty

exampleFxxyy :: GraphM Symbolic SegEqCon NodeId
exampleFxxyy = do
  x1 <- addSymbol (Symbolic "x" []) Set.empty
  y1 <- addSymbol (Symbolic "y" []) Set.empty
  z1 <- fmap (Edge (Just "fst")) (addUnion x1 y1)
  x2 <- addSymbol (Symbolic "x" []) Set.empty
  y2 <- addSymbol (Symbolic "y" []) Set.empty
  z2 <- fmap (Edge (Just "snd")) (addUnion x2 y2)
  let eq = EqCon (Seq.singleton (SegLabel "fst")) (Seq.singleton (SegLabel "snd"))
  addSymbol (Symbolic "f" [z1, z2]) (Set.singleton eq)

renderSymbolic :: Symbolic a -> Builder
renderSymbolic (Symbolic (Symbol s) _) = TLB.fromText s

renderSymbolicGraph :: NodeId -> NodeGraph Symbolic SegEqCon -> RenderM ()
renderSymbolicGraph = renderNodeGraph renderSymbolic renderEqCon
