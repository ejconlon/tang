{-# LANGUAGE OverloadedStrings #-}

module Tang.Test.UnionMap (testUm) where

import Data.Bifunctor (bimap, first)
import Data.Char (chr, ord)
import Data.Semigroup (Max)
import Data.Void (Void)
import IntLike.Map (IntLikeMap)
import IntLike.Map qualified as ILM
import IntLike.Set (IntLikeSet)
import IntLike.Set qualified as ILS
import PropUnit (TestTree, testGroup, testUnit, (===))
import Tang.Test.State (applyS, applyTestS, runS, testS)
import Tang.UnionMap qualified as UM

newtype V = V {unV :: Int}
  deriving newtype (Eq)
  deriving stock (Show)

toV :: Char -> V
toV = V . ord

fromV :: V -> Char
fromV = chr . unV

setV :: String -> IntLikeSet V
setV = ILS.fromList . fmap toV

mapV :: [(Char, a)] -> IntLikeMap V a
mapV = ILM.fromList . fmap (first toV)

mapVV :: [(Char, Char)] -> IntLikeMap V V
mapVV = ILM.fromList . fmap (bimap toV toV)

multiMapVV :: [(Char, String)] -> IntLikeMap V (IntLikeSet V)
multiMapVV = ILM.fromList . fmap (bimap toV setV)

type UMV = UM.UnionMap V (Max Int)

emptyUMV :: UMV
emptyUMV = UM.empty

mergeOneUMV :: UM.MergeOne Void (Max Int) ()
mergeOneUMV = UM.concatMergeOne

testUmSimple :: TestTree
testUmSimple = testUnit "UM simple" $ runS emptyUMV $ do
  -- start with empty map
  testS $ \um -> UM.size um === 0
  -- add 'a'
  applyTestS (UM.addM (toV 'a') 1) $ \res um -> do
    res === UM.AddValAdded
    UM.size um === 1
    UM.trace (toV 'a') um === UM.TraceResFound (toV 'a') 1 []
    UM.values um === mapV [('a', 1)]
  -- lookup 'a'
  applyTestS (UM.lookupM (toV 'a')) $ \res _ ->
    res === UM.LookupValOk (toV 'a') 1 UM.ChangedNo
  -- try to add 'a' again
  applyTestS (UM.addM (toV 'a') 1) $ \res um -> do
    res === UM.AddValDuplicate
    UM.size um === 1
  -- add 'b' and 'c' and check them
  _ <- applyS (UM.addM (toV 'b') 2)
  _ <- applyS (UM.addM (toV 'c') 3)
  testS $ \um -> do
    UM.size um === 3
    UM.trace (toV 'b') um === UM.TraceResFound (toV 'b') 2 []
    UM.trace (toV 'c') um === UM.TraceResFound (toV 'c') 3 []
    UM.values um === mapV [('a', 1), ('b', 2), ('c', 3)]
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', ""), ('b', ""), ('c', "")]
    bwd === mapVV []
  -- merge 'a' and 'c'
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'a') (toV 'c')) $ \res um -> do
    res === UM.MergeValMerged (toV 'a') 3 ()
    UM.size um === 3
    UM.trace (toV 'a') um === UM.TraceResFound (toV 'a') 3 []
    UM.trace (toV 'b') um === UM.TraceResFound (toV 'b') 2 []
    UM.trace (toV 'c') um === UM.TraceResFound (toV 'a') 3 [toV 'c']
    UM.values um === mapV [('a', 3), ('b', 2)]
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', "c"), ('b', "")]
    bwd === mapVV [('c', 'a')]
  -- try to merge again
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'a') (toV 'c')) $ \res _ ->
    res === UM.MergeValMerged (toV 'a') 3 ()
  -- and the other way around
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'c') (toV 'a')) $ \res _ ->
    res === UM.MergeValMerged (toV 'a') 3 ()
  -- and a non-existent merge
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'b') (toV 'z')) $ \res _ ->
    res === UM.MergeValMissing (toV 'z')
  -- and creating merge
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'z') (toV 'b')) $ \res _ ->
    res === UM.MergeValMerged (toV 'z') 2 ()
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', "c"), ('z', "b")]
    bwd === mapVV [('b', 'z'), ('c', 'a')]

testUmRec :: TestTree
testUmRec = testUnit "UM rec" $ runS emptyUMV $ do
  _ <- applyS (UM.addM (toV 'a') 1)
  _ <- applyS (UM.addM (toV 'b') 2)
  _ <- applyS (UM.addM (toV 'c') 3)
  _ <- applyS (UM.addM (toV 'c') 3)
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'b') (toV 'c')) $ \res um -> do
    res === UM.MergeValMerged (toV 'b') 3 ()
    UM.size um === 3
    UM.trace (toV 'a') um === UM.TraceResFound (toV 'a') 1 []
    UM.trace (toV 'b') um === UM.TraceResFound (toV 'b') 3 []
    UM.trace (toV 'c') um === UM.TraceResFound (toV 'b') 3 [toV 'c']
    UM.values um === mapV [('a', 1), ('b', 3)]
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', ""), ('b', "c")]
    bwd === mapVV [('c', 'b')]
  applyTestS (UM.mergeOneM mergeOneUMV (toV 'a') (toV 'b')) $ \res um -> do
    res === UM.MergeValMerged (toV 'a') 3 ()
    UM.size um === 3
    UM.trace (toV 'a') um === UM.TraceResFound (toV 'a') 3 []
    UM.trace (toV 'b') um === UM.TraceResFound (toV 'a') 3 [toV 'b']
    UM.trace (toV 'c') um === UM.TraceResFound (toV 'a') 3 [toV 'b', toV 'c']
    UM.values um === mapV [('a', 3)]
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', "bc")]
    bwd === mapVV [('b', 'a'), ('c', 'a')]

testUmTail :: TestTree
testUmTail = testUnit "UM tail" $ runS emptyUMV $ do
  applyS $ do
    _ <- UM.addM (toV 'a') 1
    _ <- UM.addM (toV 'b') 2
    _ <- UM.addM (toV 'c') 3
    _ <- UM.addM (toV 'd') 4
    _ <- UM.mergeOneM mergeOneUMV (toV 'c') (toV 'd')
    _ <- UM.mergeOneM mergeOneUMV (toV 'b') (toV 'c')
    _ <- UM.mergeOneM mergeOneUMV (toV 'a') (toV 'b')
    pure ()
  testS $ \um ->
    UM.trace (toV 'd') um === UM.TraceResFound (toV 'a') 4 [toV 'b', toV 'c', toV 'd']
  applyTestS UM.equivM $ \(UM.Equiv fwd bwd) _ -> do
    fwd === multiMapVV [('a', "bcd")]
    bwd === mapVV [('b', 'a'), ('c', 'a'), ('d', 'a')]
  testS $ \um ->
    UM.trace (toV 'd') um === UM.TraceResFound (toV 'a') 4 [toV 'd']

testUm :: TestTree
testUm =
  testGroup
    "UnionMap"
    [ testUmSimple
    , testUmRec
    , testUmTail
    ]
