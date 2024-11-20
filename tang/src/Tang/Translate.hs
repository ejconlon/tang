{-# LANGUAGE OverloadedStrings #-}

module Tang.Translate where

import Control.Placeholder (todo)
import Data.Foldable (traverse_)
import Data.IntMap.Strict (IntMap)
import Data.Map.Strict (Map)
import IntLike.Map qualified as ILM
import Tang.Ecta (ChildIx (..), IxEqCon, Node (..), NodeId (..), NodeMap)
import Tang.Exp (Tm (..), Ty (..), tmBv)
import Tang.Solver (SolveM, assert, defRel, defTy)
import Tang.Symbolic (Symbol (..), Symbolic (..))

ceilLog2 :: Int -> Int
ceilLog2 n = ceiling @Double @Int (logBase 2 (fromIntegral n))

maxArity :: NodeMap Symbolic IxEqCon -> Int
maxArity = todo

symTable :: NodeMap Symbolic IxEqCon -> (Map Symbol Int, IntMap Symbol)
symTable = todo

translate :: NodeMap Symbolic IxEqCon -> SolveM ()
translate nm = do
  let nidLog = ceilLog2 (ILM.size nm)
      nidTy = TyBv nidLog
      nidTm = tmBv nidLog . unNodeId
      cixMax = maxArity nm
      cixLog = ceilLog2 cixMax
      cixTy = TyBv cixLog
      cixTm = tmBv cixLog . unChildIx
      symTy = undefined
      symTm = undefined
  defTy "nid" (Just nidTy)
  defTy "cix" (Just cixTy)
  defTy "sym" (Just symTy)
  defRel "narity" ["nid", "cix"]
  defRel "nchild" ["nid", "cix", "nid"]
  defRel "nsym" ["nid", "sym"]
  -- TODO functionality should be a macro
  -- narity is functional
  -- assertForall
  --   [("n", "nid"), ("i1", "cix"), ("i2", "cix")]
  --   ( TmImplies
  --       (TmAnd [TmApp "narity" ["n", "i1"], TmApp "narity" ["n", "i2"]])
  --       (TmEq "i1" "i2")
  --   )
  -- -- nchild is functional
  -- assertForall
  --   [("n", "nid"), ("i", "cix"), ("c1", "nid"), ("c2", "nid")]
  --   ( TmImplies
  --       (TmAnd [TmApp "nchild" ["n", "i", "c1"], TmApp "nchild" ["n", "i", "c2"]])
  --       (TmEq "c1" "c2")
  --   )
  -- -- nsym is functional
  -- assertForall
  --   [("n", "nid"), ("s1", "sym"), ("s2", "sym")]
  --   ( TmImplies
  --       (TmAnd [TmApp "nsym" ["n", "s1"], TmApp "nsym" ["n", "s2"]])
  --       (TmEq "s1" "s2")
  --   )
  encodeMap nidTm cixTm symTm nm

encodeMap
  :: (NodeId -> Tm)
  -> (ChildIx -> Tm)
  -> (Symbol -> Tm)
  -> NodeMap Symbolic IxEqCon
  -> SolveM ()
encodeMap nidTm cixTm symTm = traverse_ (uncurry go) . ILM.toList
 where
  go nid = \case
    NodeSymbol _ -> todo
    NodeUnion _ -> todo
    NodeIntersect _ -> todo
