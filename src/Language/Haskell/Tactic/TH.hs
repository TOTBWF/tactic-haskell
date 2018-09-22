{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.Tactic.TH
  ( pattern Function
  , pattern Tuple
  , pattern Constructor
  , pattern List
  ) where

import Language.Haskell.TH

pattern Function t1 t2 = AppT (AppT ArrowT t1) t2

tuple :: Type -> Maybe [Type]
tuple = go []
  where
    go :: [Type] -> Type -> Maybe [Type]
    go ts (AppT (TupleT i) t) =
      let ts' = t:ts
      in (if length ts' == i then Just ts' else Nothing)
    go ts (AppT t1 t2) = go (t2:ts) t1
    go _ _ = Nothing

pattern Tuple ts <- (tuple -> Just ts)

constructor :: Type -> Maybe (Name, [Type])
constructor = go []
  where
    go :: [Type] -> Type -> Maybe (Name, [Type])
    go ts (AppT (ConT n) t) = Just (n, t:ts)
    go ts (AppT t1 t2) = go (t2:ts) t1
    go _ _ = Nothing

pattern Constructor n ts  <- (constructor -> Just (n, ts))

pattern List t = AppT ListT t
