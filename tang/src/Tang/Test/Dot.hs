module Tang.Test.Dot (testDot) where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Text.IO qualified as TIO
import PropUnit (TestTree, testUnit)
import Tang.Ecta (GraphM, NodeGraph, NodeId, buildGraph)
import Tang.Render (RenderM, simpleEvalRenderM)
import Tang.Test.Symbolic qualified as TTS

write :: (MonadIO m) => String -> (NodeId -> NodeGraph f c -> RenderM ()) -> GraphM f c NodeId -> m ()
write n f gm =
  let (root, graph) = buildGraph gm
      m = f root graph
      fn = "dot/" ++ n ++ ".dot"
      t = simpleEvalRenderM m
  in  liftIO (TIO.writeFile fn t)

testDot :: TestTree
testDot = testUnit "dot" $ do
  write "fxx" TTS.renderSymbolicGraph TTS.exampleFxx
