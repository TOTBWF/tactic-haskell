{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.Tactic
  ( Tactic
  , (<@>)
  , try
  , exact
  , assumption
  , forall
  , intro
  , intro_
  , intros
  , intros_
  , split
  , apply
  , auto
  , tactic
  ) where

import Control.Monad.Except

import Data.Foldable
import Data.Traversable

import Language.Haskell.TH.Syntax hiding (lift)

import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import Language.Haskell.Tactic.Internal.TH
import Language.Haskell.Tactic.Internal.Tactic

-- | When the hypothesis variable passed in matches the goal type,
-- discharge the goal and create no new subgoals.
exact :: String -> Tactic ()
exact n = mkTactic $ \j@(Judgement hy g) ->
  case J.lookup n j of
    Just (x, t) -> if (t == g) then return (VarE x) else throwError $ TypeMismatch g (VarE x) t
    Nothing -> throwError $ UndefinedHypothesis n

-- | Searches the hypotheses, looking for one that matches the goal type.
assumption :: Tactic ()
assumption = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find (== g) hy of
    Just (x,_) -> return $ VarE x
    Nothing -> throwError $ GoalMismatch "assumption" g

-- | Used to discharge any @forall@ statements at the begining
-- of a polymorphic type signature. This will hopefully not exist
-- for too long. DO NOT APPLY TO RANKNTYPES!!!!
forall :: Tactic ()
forall = mkTactic $ \(Judgement hy g) ->
  case g of
    (ForallT _ _ t) -> do
      subgoal $ Judgement hy t
    t -> throwError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, and generates
-- a subgoal of type @t@.
intro :: String -> Tactic ()
intro n = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      x <- fresh n
      LamE [VarP x] <$> subgoal (Judgement (hy @> (x,a)) b)
      -- return $ \[body] -> LamE [VarP x] body
    t -> throwError $ GoalMismatch "intro" t

intro_ :: Tactic  ()
intro_ = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      x <- wildcard
      LamE [VarP x] <$> subgoal (Judgement (hy @> (x,a)) b)
    t -> throwError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b -> c -> ...@
-- Brings each of the variables in as a hypothesis,
-- and generates subgoals for each of them.
intros :: [String] -> Tactic ()
intros ns = traverse_ intro ns

-- | Applies to goals of the form @a -> b -> c -> ...@
-- Adds hypothesis for every single argument, and a subgoal
-- for the return type.
intros_ :: Tactic ()
intros_ = many intro_ >> pure ()

-- | Applies to goals of the form @(a,b, ..)@.
-- Generates subgoals for every type contained in the tuple.
split :: Tactic ()
split = mkTactic $ \(Judgement hy g) ->
  case g of
    (Tuple ts) -> do
      TupE <$> traverse (subgoal . Judgement hy) ts
    t -> throwError $ GoalMismatch "tuple" t

-- | When the hypothesis variable passed in refers to a function whose return type matches the goal,
-- this tactic generates subgoals for all of the argument types.
apply :: String -> Tactic ()
apply f = mkTactic $ \j@(Judgement hy g) ->
  case (J.lookup f j) of
    Just (n, (Function args ret)) | ret == g -> do
      foldl AppE (VarE n) <$> traverse (subgoal . Judgement hy) args
    Just (_, t) -> throwError $ GoalMismatch "apply" t
    Nothing -> throwError $ UndefinedHypothesis f

-- | Looks through the context, trying to find a function that could potentially be applied.
apply_ :: Tactic ()
apply_ = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find (\case (Function args ret) -> ret == g; _ -> False) hy of
    Just (n, (Function args ret)) -> do
      foldl AppE (VarE n) <$> traverse (subgoal . Judgement hy) args
    Nothing -> throwError $ GoalMismatch "apply_" g

-- | Tries to automatically solve a given goal.
auto :: Int -> Tactic ()
auto 0 = pure ()
auto n = do
  try forall
  try intros_
  try (split <!> assumption <!> apply_)
  auto (n - 1)
