-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.TH
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- =TH
-- This module exports some handy TH AST pattern synonyms
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.Tactic.Internal.TH
  ( pattern Arrow
  , pattern Function
  , pattern Tuple
  , pattern Constructor
  , pattern List
  ) where

import Data.Bifunctor

import Language.Haskell.TH

pattern Arrow t1 t2 = AppT (AppT ArrowT t1) t2

function :: Type -> Maybe ([Type], Type)
function (Arrow t1 t2) =
  let ts = go t2
  in Just $ (t1:init ts, last ts)
  where
    go :: Type -> [Type]
    go (Arrow t1 t2) = t1:go t2
    go t = [t]
function _ = Nothing

pattern Function args ret <- (function -> Just (args, ret))

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