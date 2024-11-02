{-# LANGUAGE UndecidableInstances #-}

module Tang.Enumerate where

import Control.Monad.Except (throwError)
import Control.Placeholder (todo)
import Data.Sequence qualified as Seq
import IntLike.Map qualified as ILM
import IntLike.Set qualified as ILS
import Tang.Ecta
import Tang.Search (SearchM, interleaveSeq)

newtype Fix f = Fix {unFix :: f (Fix f)}

deriving stock instance (Eq (f (Fix f))) => Eq (Fix f)

deriving stock instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

type EnumSt = ()

type EnumM = SearchM ResErr EnumSt

enumerate :: (Traversable f) => NodeGraph f (Con ResPath) -> EnumM (Fix f)
enumerate (NodeGraph r nm _) = go r
 where
  go a = case ILM.lookup a nm of
    Nothing -> throwError (ResErrNodeMissing a)
    Just (NodeInfo _ _ _ b) -> case b of
      NodeSymbol _ -> todo
      NodeChoice ns -> interleaveSeq (Seq.fromList (fmap go (ILS.toList ns)))
      NodeClone _ -> todo
