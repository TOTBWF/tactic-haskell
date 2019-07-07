-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = Tactics
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.Tactic.Internal
  ( -- * Name Management
    unique
  , fresh
   -- * Unification
  , unify
   -- * Reify Wrappers
  , lookupConstructors
  , lookupVarType
  -- , implements
  ) where

import Control.Monad.State.Strict
import Control.Monad.Except

import qualified Data.Map.Strict as Map

import ConLike
import DataCon
import HsExpr
import HsExtension
import Name
import TcEnv
import TyCon
import SrcLoc
import Type
import Unify
import Var

import Refinery.Tactic


import Language.Haskell.Tactic.T
import Language.Haskell.Tactic.Judgement
import Language.Haskell.Tactic.Patterns

-- | Tries to create a name, and fails with @'DuplicateHypothesis'@ if the name is already taken.
-- Furthermore, names that begin with '_' are reserved for wildcard names.
unique :: String -> RuleT Judgement Expr T Name
unique "" = throwError $ InvalidHypothesisName "\"\""
unique n = gets (Map.member n . boundVars) >>= \case
  True -> throwError $ DuplicateHypothesis n
  False -> do
    modify (\s -> s { boundVars = Map.insert n 1 $ boundVars s })
    lift $ freshName n

-- | Tries to create a name provided a base, potentially appending numbers to make it unique.
-- Furthermore, names that begin with '_' are reserved for wildcard names.
fresh :: String -> RuleT Judgement Expr T (String, Name)
fresh "" = throwError $ InvalidHypothesisName "\"\""
fresh n = gets (Map.lookup n . boundVars) >>= \case
  Just i -> do
    modify (\s -> s { boundVars = Map.adjust (+ 1) n $ boundVars s })
    let n' = n ++ show i
    -- TODO: What happens if someone freshens something that ends with a number?
    (n', ) <$> (lift $ freshName n')
  Nothing -> do
    modify (\s -> s { boundVars = Map.insert n 1 $ boundVars s })
    (n, ) <$> (lift $ freshName n)

-- | Tries to unify two types
unify :: Type -> Type -> RuleT Judgement Expr T ()
unify t1 t2 = case tcUnifyTy t1 t2 of
  Just unifier -> modify (\s -> s { unificationState = unionTCvSubst unifier (unificationState s) })
  Nothing -> throwError $ UnificationError t1 t2

-- | Looks up a type's constructors.
lookupConstructors :: Name -> [Type] -> RuleT Judgement Expr T [DCon]
lookupConstructors n inst = (lift $ liftTcM $ tcLookupGlobal n) >>= \case
  ATyCon con -> do
    let ctors = tyConDataCons con
    return $ fmap (\dcon -> DCon (dataConName dcon) (dataConInstOrigArgTys dcon inst)) ctors
  i -> lift $ notImplemented "lookupConstructors: TyThing" i

-- | Looks up the the type of a variable binding, along with
-- the expression form of the name
lookupVarType :: Name -> RuleT Judgement Expr T (Expr, Type)
lookupVarType n = (lift $ liftTcM $ tcLookupGlobal n) >>= \case
  AnId i -> return (HsVar NoExt (noLoc i) , varType i)
  AConLike (RealDataCon con) -> return (HsConLikeOut NoExt (RealDataCon con), dataConUserType con)
  i -> lift $ notImplemented "lookupVarType: Variable Type" i

-- -- | Check to see if a type implements a typeclass
-- implements :: Type -> Name -> RuleT Judgement Expr T Bool
-- implements ty n = lift $ liftQ $ isInstance n [ty]

-- -- | Prints a debug message as a warning
-- debugPrint :: String -> Rule ()
-- debugPrint msg = liftQ $ reportWarning $ "DEBUG:" ++ msg


-- typedDecl :: Name -> Type -> Exp -> [Dec]
-- typedDecl decName ty ext =
--   [ SigD decName ty
--   , ValD (VarP decName) (NormalB ext) []
--   ]

-- -- | @'tactic' nm [t| ty |] tac@ creates a declaration with the name @nm@ of type @ty@
-- -- by applying the tactic @tac@
-- tactic :: String -> Q Type -> Tactic () -> Q [Dec]
-- tactic nm qty tac = do
--   decName <- newName nm
--   ty <- qty
--   (ext, subgoals) <- runTactic tac $ J.empty ty
--   case subgoals of
--     [] -> do
--       return $ typedDecl decName ty ext
--     _ -> hoistError $ UnsolvedGoals subgoals


-- -- | @debugTactic nm [t| ty |] tac@ behaves exactly the same as @tactic@,
-- -- but it prints out the resulting expression as a warning.
-- debugTactic :: String -> Q Type -> Tactic () -> Q [Dec]
-- debugTactic nm qty tac = do
--   decName <- newName nm
--   ty <- qty
--   (ext, subgoals) <- runTactic tac $ J.empty ty
--   case subgoals of
--     [] -> do
--       reportWarning $ render $ ppr ext
--       return $ typedDecl decName ty ext
--     _ -> hoistError $ UnsolvedGoals subgoals
