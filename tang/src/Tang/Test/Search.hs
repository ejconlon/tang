{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Monad law, right identity" #-}

module Tang.Test.Search (testSearch) where

import Control.Applicative (Alternative (..))
import Control.Monad (replicateM_)
import Control.Monad.Identity (runIdentity)
import Control.Monad.Logic (MonadLogic (..), reflect)
import Control.Monad.State.Strict (get, modify', put)
import Data.Sequence qualified as Seq
import PropUnit (TestTree, testUnit, (===))
import Tang.Search (SearchM, interleaveSeq, searchN)

type M = SearchM String () Int

type Res a = (Either String a, Int)

simple :: [Int] -> [Res Int]
simple = fmap (\a -> (Right a, 0))

rights :: [Int] -> [Res Int]
rights = fmap (\i -> (Right i, i))

inc :: M ()
inc = modify' (+ 1)

run :: M a -> [(Either String a, Int)]
run m = runIdentity (searchN 100 m () 0)

testSearch :: TestTree
testSearch = testUnit "Search" $ do
  let res0 = simple [2, 1]
      res1 = simple [1, 2, 3]
      res2 = simple [1, 3, 2]
      res3 = rights [2, 1]
  run (pure 2 <|> pure 1) === res0
  run (pure 1 <|> (pure 2 <|> pure 3)) === res1
  run ((pure 1 <|> pure 2) <|> pure 3) === res1
  run (interleave (pure 2) (pure 1)) === res0
  run (interleave (pure 1) (interleave (pure 2) (pure 3))) === res1
  run (interleave (interleave (pure 1) (pure 2)) (pure 3)) === res2
  run trackAlt0 === res3
  run trackAlt1 === res3
  run trackAlt2 === res3
  run trackAlt3 === res3
  run trackSplit0 === res3
  run (splitRef trackAlt0) === res3
  run (splitRef trackAlt1) === res3
  run (splitRef trackAlt2) === res3
  run (splitRef trackAlt3) === res3
  run (trackAlt0 >>= pure) === res3
  run (trackAlt0 >>- pure) === res3
  run (trackAlt1 >>= pure) === res3
  run (trackAlt1 >>- pure) === res3
  run (trackAlt2 >>= pure) === res3
  run (trackAlt2 >>- pure) === res3
  run (trackAlt3 >>= pure) === res3
  run (trackAlt3 >>- pure) === res3
  run trackInt0 === res3
  run trackInt1 === res3
  run trackInt2 === res3
  run trackInt3 === res3
  run trackFair0 === rights [3, 2, 1]
  run trackFair1 === rights [3, 2, 4, 1, 3, 2]
  run trackSplitEff0 === rights [1, 0]
  run trackSplitEff1 === rights [1, 0]
  run trackSplitEff2 === rights [2, 0]
  run trackSplitEff3 === rights [2, 0]
  run trackIntMulti0 === rights [2, 0, 1]
  run (interleaveSeq (Seq.fromList (fmap (\i -> i <$ put i) [0, 1, 2, 3, 4]))) === rights [0, 2, 1, 3, 4]

-- split-reflect - should be identical to m, let's test that it really is
splitRef :: M a -> M a
splitRef m = msplit m >>= reflect

-- This should behave like trackAlt0
trackSplit0 :: M Int
trackSplit0 = inc >> splitRef ((inc >> get) <|> get)

-- These are the alt versions of the interleaving versions below
trackAlt0, trackAlt1, trackAlt2, trackAlt3 :: M Int
trackAlt0 = inc >> ((inc >> get) <|> get)
trackAlt1 = (inc >> inc >> get) <|> (inc >> get)
trackAlt2 = ((inc >> inc) <|> inc) >> get
trackAlt3 = (inc <|> pure ()) >> inc >> get

-- These are the interleaving versions of the alt versions above
trackInt0, trackInt1, trackInt2, trackInt3 :: M Int
trackInt0 = inc >> interleave (inc >> get) get
trackInt1 = interleave (inc >> inc >> get) (inc >> get)
trackInt2 = interleave (inc >> inc) inc >> get
trackInt3 = interleave inc (pure ()) >> inc >> get

trackList :: [Int] -> M Int
trackList = foldr1 (<|>) . fmap pure

trackFair0, trackFair1 :: M Int
trackFair0 =
  trackList [3, 2, 1] >>- \n ->
    replicateM_ n inc >> get
trackFair1 =
  trackList [3, 2, 1] >>- \n ->
    replicateM_ n inc >> (get <|> (inc >> get))

trackSplitEff0 :: M Int
trackSplitEff0 = do
  mp <- msplit ((inc >> pure 0) <|> get)
  case mp of
    Nothing -> empty
    Just (_, rest) -> get <|> rest

trackSplitEff1 :: M Int
trackSplitEff1 = do
  mp <- msplit (interleave (inc >> pure 0) get)
  case mp of
    Nothing -> empty
    Just (_, rest) -> get <|> rest

trackSplitEff2 :: M Int
trackSplitEff2 = do
  mp <- msplit ((inc >> pure 0) <|> get)
  case mp of
    Nothing -> empty
    Just (_, rest) -> inc >> (get <|> rest)

trackSplitEff3 :: M Int
trackSplitEff3 = do
  mp <- msplit (interleave (inc >> pure 0) get)
  case mp of
    Nothing -> empty
    Just (_, rest) -> inc >> (get <|> rest)

trackIntMulti0 :: M Int
trackIntMulti0 = interleave ((inc >> inc >> get) <|> (inc >> get)) get
