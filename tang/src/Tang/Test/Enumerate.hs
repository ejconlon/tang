{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Enumerate
  ( testEnumerate
  , exampleX
  , exampleFxx
  , exampleFxxyy
  , buildIxGraph
  )
where

import Control.Exception (throwIO)
import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader (Reader, asks, runReader)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text (Text)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import Prettyprinter (Doc, defaultLayoutOptions, layoutSmart)
import Prettyprinter.Render.Text (renderStrict)
import PropUnit (PropertyT, TestName, TestTree, testGroup, testUnit, (===))
import Tang.Align (Alignable)
import Tang.Ecta
  ( Edge (..)
  , EqCon (..)
  , GraphM
  , IxEqCon
  , NodeGraph
  , NodeId
  , Seg (..)
  , SegEqCon
  , addSymbol
  , addUnion
  , buildGraph
  , eqConT
  , ngRewriteSeg
  )
import Tang.Enumerate (Elem (..), ElemInfo (..), EnumErr, EnumSt, Synth (..), SynthId (..), enumerate)
import Tang.Search (SearchStrat (..))
import Tang.Symbolic (Symbolic (..), symPrettyM)

-- TODO move to lib
type EnumStrat e f = SearchStrat (EnumErr e) (EnumSt f IxEqCon) (Synth f)

type RenderM = Reader (IntLikeMap SynthId (ElemInfo Symbolic))

synthDoc :: Synth Symbolic -> Doc ann
synthDoc (Synth root dag) = runReader (go root) dag
 where
  go sid = do
    mx <- asks (ILM.lookup sid)
    case mx of
      Nothing -> error "bad graph"
      Just (ElemInfo _ el) -> case el of
        ElemMeta -> pure "*"
        ElemNode fs -> symPrettyM go fs

synthText :: Synth Symbolic -> Text
synthText = renderStrict . layoutSmart defaultLayoutOptions . synthDoc

buildIxGraph
  :: (MonadIO m)
  => GraphM f SegEqCon NodeId
  -> m (NodeId, NodeGraph f IxEqCon)
buildIxGraph graph =
  let (a, ngBySeg) = buildGraph graph
      ex = runExcept (ngRewriteSeg eqConT ngBySeg)
  in  either (liftIO . throwIO) (pure . (a,)) ex

data EnumCase where
  EnumCase
    :: (Alignable e f)
    => TestName
    -> EnumStrat e f x
    -> GraphM f SegEqCon NodeId
    -> (x -> PropertyT IO ())
    -> EnumCase

runEnumCase :: EnumCase -> TestTree
runEnumCase (EnumCase name strat graph kont) =
  testUnit name $ do
    (root, ngByIx) <- buildIxGraph graph
    kont (enumerate strat root ngByIx)

mkSynthCase :: TestName -> [Text] -> GraphM Symbolic SegEqCon NodeId -> EnumCase
mkSynthCase name results graph =
  let lim = 1000
  in  EnumCase name (SearchStratN lim) graph $ \xs ->
        case mapM fst xs of
          Left e -> liftIO (throwIO e)
          Right as -> do
            let expected = Set.fromList results
                actual = Set.fromList (fmap synthText as)
            -- liftIO $ do
            --   putStr "graphs:   " >> print as
            --   putStr "expected: " >> print expected
            --   putStr "actual:   " >> print actual
            expected === actual

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

enumCases :: [EnumCase]
enumCases =
  [ EnumCase "basic" SearchStratAll exampleX $ \case
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
  , mkSynthCase "x again" ["(x)"] exampleX
  , mkSynthCase "fxx" ["(f (x) (x))"] exampleFxx
  , mkSynthCase "fxx|fyy" ["(f (x) (x))", "(f (y) (y))"] exampleFxxyy
  ]

testEnumerate :: TestTree
testEnumerate = testGroup "enumerate" (fmap runEnumCase enumCases)
