
-- |
-- Module      :  Language.Haskell.Tactic.T
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Tactic.T
  ( T(..)
  , TacticState(..)
  , TacticError(..)
  , freshName
  , notImplemented
  , liftTcM
  ) where

import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad.Fail (MonadFail)


import Data.Map.Strict (Map)

import Outputable (Outputable(..), (<+>), ($+$))
import qualified Outputable as P

import DynFlags
import Name
import TcRnMonad
import Type

import Language.Haskell.Tactic.Judgement
import Refinery.Tactic

data TacticState = TacticState
  { boundVars :: Map String Int
  , unificationState :: TCvSubst
  }


-- NOTE: Should I just handle everything as IORefs?
-- I could handle backtracking state using a custom `catchError`

newtype T a = T { unT :: StateT TacticState (ExceptT TacticError TcM) a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadState TacticState, MonadError TacticError)

instance MonadProvable Judgement T where
  proving j = do
    unifier <- gets unificationState
    pure $ substJdg unifier j

freshName :: String -> T Name
freshName nm = T $ lift $ lift $ newName $ mkVarOcc nm

liftTcM :: TcM a -> T a
liftTcM m = T $ lift $ lift m

data TacticError
  = TypeMismatch { expectedType :: Type, expr :: Expr, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UndefinedHypothesis String
  | DuplicateHypothesis String
  | InvalidHypothesisName String
  | UnsolvedGoals [Judgement]
  | UnificationError Type Type
  | NoProgress
  | NoApplicableTactic
  | NotImplemented String

instance Outputable TacticError where
  ppr = \case
    TypeMismatch{ expectedType, expr, exprType } ->
      P.text "Expected Type" <+> ppr expectedType <+> P.text "but" <+> ppr expr <+> P.text "has type" <+> ppr exprType
    GoalMismatch{ tacName, appliedGoal } ->
      P.text "Tactic" <+> P.text tacName <+> P.text "doesn't support goals of the form" <+> ppr appliedGoal
    UndefinedHypothesis v ->
      P.text "Undefined Hypothesis" <+> P.text v
    DuplicateHypothesis v ->
      P.text "Duplicate Hypothesis" <+> P.text v
    InvalidHypothesisName v ->
      P.text "Invalid Hypothesis Name" <+> P.text v
    UnsolvedGoals ps ->
      P.text "Unsolved Subgoals" $+$ ppr ps
    UnificationError t1 t2 ->
      P.text "Unification Error:" <+> ppr t1 <+> P.text "and" <+> ppr t2
    NoProgress -> P.text "No Progress"
    NoApplicableTactic -> P.text "No Applicable Tactic"
    NotImplemented t -> P.text t <+> P.text "isn't implemented yet"

notImplemented :: (Outputable a) => String -> a -> T b
notImplemented msg a = do
  dynflags <- liftTcM $ getDynFlags
  throwError $ NotImplemented $ msg ++ " " ++ (P.showSDoc dynflags (ppr a))
