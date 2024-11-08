{-# LANGUAGE OverloadedStrings #-}

module Tang.Dot where

import Control.Monad (unless)
import Data.Foldable (for_, toList)
import Data.List (intersperse)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set (Set)
import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as TLB
import IntLike.Map qualified as ILM
import IntLike.Set qualified as ILS
import Tang.Ecta
  ( ChildIx (..)
  , EqCon (..)
  , Label (..)
  , Node (..)
  , NodeGraph (..)
  , NodeId (..)
  , Seg (..)
  , SegEqCon
  , SegPath
  , SymbolNode (..)
  )
import Tang.Render (RenderM, fromShowable, renderBuilder, renderBuilders)
import Tang.Util (forWithIndex_)

type Attrs = Map Text [Text]

symbolNodeAttrs :: Attrs
symbolNodeAttrs = Map.fromList [("shape", ["circle"])]

unionNodeAttrs :: Attrs
unionNodeAttrs = Map.fromList [("shape", ["square"])]

intersectNodeAttrs :: Attrs
intersectNodeAttrs = Map.fromList [("shape", ["diamond"])]

cloneNodeAttrs :: Attrs
cloneNodeAttrs = Map.fromList [("shape", ["octagon"])]

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

renderEdge :: Builder -> Builder -> Maybe Builder -> Attrs -> RenderM ()
renderEdge nidSrc nidDest mlab attrs = do
  renderBuilders ["  ", nidSrc, " -> ", nidDest]
  unless (Map.null attrs && isNothing mlab) $ do
    let labb = maybe mempty (\l -> "label=\"" <> l <> "\" ") mlab
        atb = fromAttrs attrs
    renderBuilders [" [", labb, atb, "]"]
  renderBuilder "\n"

renderSeg :: Seg -> Builder
renderSeg = \case
  SegLabel (Label x) -> TLB.fromText x
  SegIndex (ChildIx x) -> TLB.fromString (show x)

renderPath :: SegPath -> Builder
renderPath = mconcat . intersperse (TLB.singleton '.') . fmap renderSeg . toList

renderEqCon :: SegEqCon -> Builder
renderEqCon = \case
  EqCon p1 p2 -> renderPath p1 <> " = " <> renderPath p2

renderCons :: (c -> Builder) -> Set c -> Builder
renderCons f = mconcat . intersperse (TLB.singleton '\n') . fmap f . toList

renderNodeGraph :: (Foldable f) => (f NodeId -> Builder) -> (c -> Builder) -> NodeId -> NodeGraph f c -> RenderM ()
renderNodeGraph g f root (NodeGraph _ nm _) = do
  renderBuilder "digraph g {\n"
  -- Emit nodes
  for_ (ILM.toList nm) $ \(i, n) -> do
    let nid = fromShowable (unNodeId i)
        (nlab, mxlab, attrs) = case n of
          NodeSymbol (SymbolNode _ _ _ fe cs) ->
            (g fe, Just (renderCons f cs), symbolNodeAttrs)
          NodeUnion _ -> do
            ("", Nothing, unionNodeAttrs)
          NodeIntersect _ -> do
            ("", Nothing, intersectNodeAttrs)
          NodeClone _ -> do
            ("", Nothing, cloneNodeAttrs)
        attrs' = attrs <> (if i == root then rootNodeAttrs else mempty)
    renderNode nid nlab mxlab attrs'
  -- Emit edges
  for_ (ILM.toList nm) $ \(i, n) -> do
    let nid = fromShowable (unNodeId i)
    case n of
      NodeSymbol (SymbolNode _ _ ixLab fn _) -> do
        forWithIndex_ fn $ \ix cid -> do
          let mlab = fmap (TLB.fromText . unLabel) (ILM.lookup (ChildIx ix) ixLab)
              cidb = fromShowable (unNodeId cid)
          renderEdge nid cidb mlab normalEdgeAttrs
      NodeUnion js ->
        for_ (ILS.toList js) $ \j -> do
          let cidb = fromShowable (unNodeId j)
          renderEdge nid cidb Nothing normalEdgeAttrs
      NodeIntersect js ->
        for_ (ILS.toList js) $ \j -> do
          let cidb = fromShowable (unNodeId j)
          renderEdge nid cidb Nothing normalEdgeAttrs
      NodeClone j -> do
        let cidb = fromShowable (unNodeId j)
        renderEdge nid cidb Nothing cloneEdgeAttrs
  renderBuilder "}\n"
