{-# LANGUAGE OverloadedStrings #-}

module Tang.Dot where

import Control.Monad (unless)
import Data.Foldable (for_, toList)
import Data.List (intersperse)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import IntLike.Map qualified as ILM
import Tang.Ecta
  ( ChildIx (..)
  , Con (..)
  , Edge (..)
  , Label (..)
  , Node (..)
  , NodeGraph (..)
  , NodeId (..)
  , NodeInfo (..)
  , Path
  , Seg (..)
  , SymbolNode (..)
  )
import Tang.Render (RenderM, fromShowable, renderBuilder, renderBuilders)

type Attrs = Map Text [Text]

symbolNodeAttrs :: Attrs
symbolNodeAttrs = Map.empty

choiceNodeAttrs :: Attrs
choiceNodeAttrs = Map.empty

cloneNodeAttrs :: Attrs
cloneNodeAttrs = Map.empty

rootNodeAttrs :: Attrs
rootNodeAttrs = Map.fromList [("style", ["bold"])]

normalEdgeAttrs :: Attrs
normalEdgeAttrs = Map.empty

cloneEdgeAttrs :: Attrs
cloneEdgeAttrs = Map.fromList [("style", ["dashed"])]

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
  renderBuilders ["  ", nid, " [forcelabels=\"true\" label=\"", nlab, "\""]
  for_ mxlab $ \xlab ->
    renderBuilders [" ", "xlabel=\"", xlab, "\""]
  unless (Map.null attrs) $
    renderBuilders [" ", fromAttrs attrs]
  renderBuilder "]\n"

renderEdge :: Builder -> Builder -> Attrs -> RenderM ()
renderEdge nidSrc nidDest attrs = do
  renderBuilders ["  ", nidSrc, " -> ", nidDest]
  unless (Map.null attrs) $
    renderBuilders [" [", fromAttrs attrs, "]"]
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

renderNodeGraph :: (f Edge -> Builder) -> (c -> Builder) -> NodeGraph f c -> RenderM ()
renderNodeGraph g _f (NodeGraph root m _) = do
  renderBuilder "digraph g {\n"
  -- Emit nodes
  for_ (ILM.toList m) $ \(i, NodeInfo _ _ _ n) -> do
    let nid = fromShowable (unNodeId i)
        (nlab, mxlab, attrs) = case n of
          NodeSymbol (SymbolNode _ fe) ->
            (g fe, Nothing, symbolNodeAttrs)
          NodeChoice _ -> do
            ("", Nothing, choiceNodeAttrs)
          NodeClone _ -> do
            ("", Nothing, cloneNodeAttrs)
    let attrs' = attrs <> (if i == root then rootNodeAttrs else mempty)
    renderNode nid nlab mxlab attrs'
  -- Emit edges
  -- for_ (ILM.toList m) $ \(NodeId i, NodeInfo _sz _chi n) -> do
  --   let _nid = fromShowable i
  --   case n of
  --     NodeSymbol (SymbolNode _ _fe) ->
  --       todo
  --     NodeChoice _js ->
  --       todo
  --     NodeClone _j ->
  --       todo
  renderBuilder "}\n"
