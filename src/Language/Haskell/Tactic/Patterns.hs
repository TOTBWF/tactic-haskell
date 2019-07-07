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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.Tactic.Patterns
  ( pattern Function
  , pattern Tuple
  , pattern Constructor
  , Expr
  , DCon(..)
  , var
  , lam
  , tuple
  , app
  ) where

import BasicTypes
import Name
import HsBinds
import HsExpr
import HsExtension
import HsPat
import SrcLoc
import TyCon
import TyCoRep
import Var

type Expr = HsExpr (GhcPass 'Typechecked)

function :: Type -> Maybe ([Type], Type)
function (ForAllTy _ t) = function t
function (FunTy t1 t2) =
  let ts = go t2
  in Just $ (t1:init ts, last ts)
  where
    go :: Type -> [Type]
    go (FunTy t1 t2) = t1:go t2
    go t = [t]
function _ = Nothing

-- | Pattern for a function of any given arity
pattern Function :: [Type] -> Type -> Type
pattern Function args ret <- (function -> Just (args, ret))

tupleTy :: Type -> Maybe [Type]
tupleTy (TyConApp tycon ts) | isTupleTyCon tycon = Just ts
tupleTy _ = Nothing

-- | Pattern for a tuple of any given arity
pattern Tuple :: [Type] -> Type
pattern Tuple ts <- (tupleTy -> Just ts)

constructor :: Type -> Maybe (Name, [Type])
constructor (TyConApp tycon tvs) = Just (tyConName tycon, tvs)
constructor _ = Nothing

-- | Pattern for a constructor application
pattern Constructor :: Name -> [Type] -> Type
pattern Constructor n ts  <- (constructor -> Just (n, ts))

-- | Simple Data Constructor Type
data DCon = DCon Name [Type]

var :: Var -> Expr
var v = HsVar NoExt (noLoc v)

lam :: Var -> Type -> Type -> Expr -> Expr
lam v a b body =
  let rhs = GRHSs NoExt [noLoc $ GRHS NoExt [] (noLoc body)] (noLoc $ EmptyLocalBinds NoExt)
      vpat = [noLoc $ VarPat NoExt (noLoc v)]
      ty = MatchGroupTc [a] b
  in HsLam NoExt $ MG ty (noLoc [noLoc $ Match NoExt LambdaExpr vpat rhs]) Generated

tuple :: [Expr] -> Expr
tuple exprs = ExplicitTuple NoExt (fmap (noLoc . Present NoExt . noLoc) exprs) Boxed

app :: Expr -> Expr -> Expr
app e1 e2 = HsApp NoExt (noLoc e1) (noLoc e2)