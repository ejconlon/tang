{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Enumerate (testEnumerate) where

import Control.Exception (throwIO)
import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (liftIO)
import Data.Sequence (Seq (..))
import Data.Text (Text)
import IntLike.Map qualified as ILM
import Prettyprinter (defaultLayoutOptions, layoutSmart, Doc)
import Prettyprinter.Render.Text (renderStrict)
import PropUnit (PropertyT, TestName, TestTree, testGroup, testUnit, (===))
import Tang.Align (Alignable)
import Tang.Ecta (GraphM, IxEqCon, NodeId, SegEqCon, buildGraph, eqConT, ngRewriteSeg)
import Tang.Enumerate (Elem (..), ElemInfo (..), EnumErr, EnumSt, Synth (..), SynthId (..), enumerate)
import Tang.Search (SearchStrat (..))
import Tang.Test.Symbolic (Symbolic (..), exampleX, symPrettyM, exampleFxx)
import IntLike.Map (IntLikeMap)
import Control.Monad.Reader (Reader, runReader, asks)
import qualified Data.Set as Set

-- TODO move to lib
type EnumStrat e f = SearchStrat (EnumErr e) (EnumSt f IxEqCon) (Synth f)

type RenderM = Reader (IntLikeMap SynthId (ElemInfo Symbolic))

synthDoc :: Synth Symbolic -> Doc ann
synthDoc (Synth root dag) = runReader (go root) dag where
  go sid = do
    mx <- asks (ILM.lookup sid)
    case mx of
      Nothing -> error "bad graph"
      Just (ElemInfo _ el) -> case el of
        ElemMeta -> pure "*"
        ElemNode fs -> symPrettyM go fs

synthText :: Synth Symbolic -> Text
synthText = renderStrict . layoutSmart defaultLayoutOptions . synthDoc

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
  testUnit name $
    let (root, ngBySeg) = buildGraph graph
    in  case runExcept (ngRewriteSeg eqConT ngBySeg) of
          Left e -> liftIO (throwIO e)
          Right ngByIx -> do
            let x = enumerate strat root ngByIx
            kont x

mkSynthCase :: TestName -> [Text] -> GraphM Symbolic SegEqCon NodeId -> EnumCase
mkSynthCase name results graph =
  let lim = 1000
  in EnumCase name (SearchStratN lim) graph $ \xs ->
    case mapM fst xs of
      Left e -> liftIO (throwIO e)
      Right as ->
        let expected = Set.fromList results
            actual = Set.fromList (fmap synthText as)
        in expected === actual

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
  ]

testEnumerate :: TestTree
testEnumerate = testGroup "enumerate" (fmap runEnumCase enumCases)
