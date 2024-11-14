{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Symbolic where

import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import Prettyprinter (Doc, Pretty (..))
import Prettyprinter qualified as P
import Tang.Align (Alignable (..), EqAlignErr, eqAlignWithM)
import Tang.Dot (renderEqCon, renderNodeGraph)
import Tang.Ecta (Edge (..), GraphM, NodeGraph, NodeId, SegEqCon, addSymbol)
import Tang.Render (RenderM)
import Data.Functor ((<&>))
import Control.Monad.Identity (Identity(..))

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

renderSymbolic :: Symbolic a -> Builder
renderSymbolic (Symbolic (Symbol s) _) = TLB.fromText s

renderSymbolicGraph :: NodeId -> NodeGraph Symbolic SegEqCon -> RenderM ()
renderSymbolicGraph = renderNodeGraph renderSymbolic renderEqCon
