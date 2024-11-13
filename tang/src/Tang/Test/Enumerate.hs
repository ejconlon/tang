{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Enumerate (testEnumerate) where

import Control.Exception (throwIO)
import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (liftIO)
import Data.Sequence (Seq (..))
import IntLike.Map qualified as ILM
import PropUnit (PropertyT, TestTree, testUnit, (===))
import Tang.Align (Alignable)
import Tang.Ecta (GraphM, IxEqCon, NodeId, SegEqCon, buildGraph, eqConT, ngRewriteSeg)
import Tang.Enumerate (Elem (..), ElemInfo (..), EnumErr, EnumSt, Synth (..), SynthId (..), enumerate)
import Tang.Search (SearchStrat (..))
import Tang.Test.Symbolic (Symbolic (..), exampleX)

-- TODO move to lib
type EnumStrat e f = SearchStrat (EnumErr e) (EnumSt f IxEqCon) (Synth f)

runEnum :: (Alignable e f) => EnumStrat e f x -> GraphM f SegEqCon NodeId -> (x -> PropertyT IO ()) -> PropertyT IO ()
runEnum strat graph kont = do
  let (root, ngBySeg) = buildGraph graph
  case runExcept (ngRewriteSeg eqConT ngBySeg) of
    Left e -> liftIO (throwIO e)
    Right ngByIx -> do
      let x = enumerate strat root ngByIx
      kont x

testEnumerate :: TestTree
testEnumerate = testUnit "enumerate" $ do
  runEnum SearchStratAll exampleX $ \case
    [(ea, _)] -> case ea of
      Left e -> liftIO (throwIO e)
      Right (Synth r m) -> do
        ILM.size m === 1
        case ILM.lookup r m of
          Nothing -> fail "bad graph"
          Just (ElemInfo _ el) ->
            case el of
              ElemMeta -> fail "unsolved meta"
              ElemNode (Symbolic hd tl) -> do
                hd === "x"
                tl === Empty
    _ -> fail "expected singleton"
