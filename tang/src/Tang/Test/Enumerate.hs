{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.Enumerate (testEnumerate) where

import Control.Exception (throwIO)
import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (liftIO)
import Data.Coerce (Coercible, coerce)
import Data.Sequence (Seq (..))
import Data.Text (Text)
import IntLike.Map qualified as ILM
import Prettyprinter (Pretty (..), defaultLayoutOptions, layoutSmart)
import Prettyprinter.Render.Text (renderStrict)
import PropUnit (PropertyT, TestName, TestTree, testGroup, testUnit, (===))
import Tang.Align (Alignable)
import Tang.Ecta (GraphM, IxEqCon, NodeId, SegEqCon, buildGraph, eqConT, ngRewriteSeg)
import Tang.Enumerate (Elem (..), ElemInfo (..), EnumErr, EnumSt, Synth (..), SynthId (..), enumerate)
import Tang.Search (SearchStrat (..))
import Tang.Test.Symbolic (Symbolic (..), exampleX, symPretty)

-- TODO move to lib
type EnumStrat e f = SearchStrat (EnumErr e) (EnumSt f IxEqCon) (Synth f)

symText :: (Coercible k Int) => Symbolic k -> Text
symText = renderStrict . layoutSmart defaultLayoutOptions . symPretty (pretty . coerce @_ @Int)

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
  ]

testEnumerate :: TestTree
testEnumerate = testGroup "enumerate" (fmap runEnumCase enumCases)
