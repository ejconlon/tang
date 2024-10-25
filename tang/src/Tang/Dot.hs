{-# LANGUAGE OverloadedStrings #-}

module Tang.Dot where

import Control.Monad (unless)
import Data.Coerce (Coercible)
import Data.Foldable (for_, toList)
import Data.List (intersperse)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import Tang.Ecta
  ( ChildIx (..)
  , Con (..)
  , Edge (..)
  , Label (..)
  , Node (..)
  , NodeId (..)
  , NodeInfo (..)
  , NodeMap
  , Path
  , Seg (..)
  , Symbol (..)
  , SymbolNode (..)
  )
import Tang.Render (RenderM, fromShowable, renderBuilder, renderBuilders, renderText)

type Attrs = Map Text [Text]

-- decNodeAttrs :: Attrs
-- decNodeAttrs = Map.fromList
--   [ ("shape", ["circle"])
--   , ("style", ["filled", "dashed"])
--   , ("fillcolor", ["white"])
--   , ("color", ["red"])
--   , ("fontcolor", ["red"])
--   ]
--
-- decEdgeAttrs :: Attrs
-- decEdgeAttrs = Map.fromList
--   [ ("style", ["dashed"])
--   , ("color", ["red"])
--   ]
--
-- conNodeAttrs :: Attrs
-- conNodeAttrs = Map.fromList
--   [ ("shape", ["circle"])
--   , ("style", ["filled", "solid"])
--   , ("fillcolor", ["white"])
--   , ("color", ["blue"])
--   , ("fontcolor", ["blue"])
--   ]
--
-- conEdgeAttrs :: Attrs
-- conEdgeAttrs = Map.fromList
--   [ ("style", ["solid"])
--   , ("color", ["blue"])
--   ]

cloneEdgeAttrs :: Attrs
cloneEdgeAttrs = Map.empty

fromAttrs :: Attrs -> Builder
fromAttrs attrs = buildAttrs (Map.toList attrs)
 where
  spaceBuilder = TLB.singleton ' '
  eqBuilder = TLB.singleton '='
  quotBuilder = TLB.fromText "\""
  buildAttrs = mconcat . intersperse spaceBuilder . fmap buildAttr
  buildAttr (k, vs) = TLB.fromText k <> eqBuilder <> buildValues vs
  buildValues vs = mconcat (intersperse spaceBuilder (fmap (\v -> quotBuilder <> TLB.fromText v <> quotBuilder) vs))

renderNode :: Builder -> Builder -> Maybe Builder -> Attrs -> RenderM ()
renderNode nid nlab mxlab attrs = do
  renderBuilders ["  ", nid, "[forcelabels=true label=\"", nlab, "\""]
  for_ mxlab $ \xlab ->
    renderBuilders [" ", "xlabel=\"", xlab, "\""]
  unless (Map.null attrs) $
    renderBuilders [" ", fromAttrs attrs]
  renderBuilder "]\n"

renderEdge :: Builder -> Builder -> Attrs -> RenderM ()
renderEdge nidSrc nidDest attrs = do
  renderBuilders ["  ", nidSrc, " -> ", nidDest]
  unless (Map.null attrs) $
    renderBuilders ["[", fromAttrs attrs, "]"]
  renderBuilder "\n"

renderSeg :: Seg -> Builder
renderSeg = \case
  SegLabel (Label x) -> TLB.fromText x
  SegIndex (ChildIx x) -> TLB.fromString (show x)

renderPath :: Path -> Builder
renderPath = mconcat . intersperse (TLB.singleton '.') . fmap renderSeg . toList

renderCon :: Con Path -> Builder
renderCon = \case
  ConEq p1 p2 -> renderPath p1 <> " = " <> renderPath p2

renderNodeMap :: (f Edge -> Builder) -> (c -> Builder) -> NodeMap f c -> RenderM ()
renderNodeMap g f m = do
  renderBuilder "digraph g {\n"
  for_ (ILM.toList m) $ \(NodeId i, NodeInfo n _) -> do
    let it = fromShowable i
    case n of
      NodeSymbol (SymbolNode _ _) -> error "TODO"
      NodeChoice _ -> error "TODO"
      NodeClone (NodeId j) -> renderEdge it (fromShowable j) cloneEdgeAttrs
    pure ()
  renderBuilder "}\n"
