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
  , (<..>)
  , (?)
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

import Control.Applicative

import Data.Foldable

import Language.Haskell.TH.Syntax hiding (lift)

import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import Language.Haskell.Tactic.Internal.TH
import Language.Haskell.Tactic.Internal.Tactic

-- | When the hypothesis variable passed in matches the goal type,
-- discharge the goal and create no new subgoals.
exact :: String -> Tactic Judgement ()
exact n = mkTactic $ \j@(Judgement hy g) ->
  case J.lookup n j of
    Just (x, t) -> if (t == g) then return (\_ -> VarE x) else tacticError $ TypeMismatch g (VarE x) t
    Nothing -> tacticError $ UndefinedHypothesis n

-- | Searches the hypotheses, looking for one that matches the goal type.
assumption :: Tactic Judgement ()
assumption = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find (== g) hy of
    Just (x,_) -> return (\_ -> VarE x)
    Nothing -> tacticError $ GoalMismatch "assumption" g

-- | Used to discharge any @forall@ statements at the begining
-- of a polymorphic type signature. This will hopefully not exist
-- for too long. DO NOT APPLY TO RANKNTYPES!!!!
forall :: Tactic Judgement ()
forall = mkTactic $ \(Judgement hy g) ->
  case g of
    (ForallT _ _ t) -> do
      subgoal $ Judgement hy t
      return $ head
    t -> tacticError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, and generates
-- a subgoal of type @t@.
intro :: String -> Tactic Judgement ()
intro n = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      x <- fresh n
      subgoal (Judgement (hy @> (x,a)) b)
      return $ \[body] -> LamE [VarP x] body
    t -> tacticError $ GoalMismatch "intro" t

intro_ :: Tactic Judgement ()
intro_ = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      x <- wildcard
      subgoal (Judgement (hy @> (x,a)) b)
      return $ \[body] -> LamE [VarP x] body
    t -> tacticError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b -> c -> ...@
-- Brings each of the variables in as a hypothesis,
-- and generates subgoals for each of them.
intros :: [String] -> Tactic Judgement ()
intros ns = traverse_ intro ns

-- | Applies to goals of the form @a -> b -> c -> ...@
-- Adds hypothesis for every single argument, and a subgoal
-- for the return type.
intros_ :: Tactic Judgement ()
intros_ = many intro_ >> pure ()

-- | Applies to goals of the form @(a,b, ..)@.
-- Generates subgoals for every type contained in the tuple.
split :: Tactic Judgement ()
split = mkTactic $ \(Judgement hy g) ->
  case g of
    (Tuple ts) -> do
      traverse_ (subgoal . Judgement hy) ts
      return TupE
    t -> tacticError $ GoalMismatch "tuple" t

-- | When the hypothesis variable passed in refers to a function whose return type matches the goal,
-- this tactic generates subgoals for all of the argument types.
apply :: String -> Tactic Judgement ()
apply f = mkTactic $ \j@(Judgement hy g) ->
  case (J.lookup f j) of
    Just (n, (Function args ret)) | ret == g -> do
      traverse_ (subgoal . Judgement hy) args
      return $ foldl AppE (VarE n)
    Just (_, t) -> tacticError $ GoalMismatch "apply" t
    Nothing -> tacticError $ UndefinedHypothesis f

-- | Looks through the context, trying to find a function that could potentially be applied.
apply_ :: Tactic Judgement ()
apply_ = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find (\case (Function args ret) -> ret == g; _ -> False) hy of
    Just (n, (Function args ret)) -> do
      traverse_ (subgoal . Judgement hy) args
      return $ foldl AppE (VarE n)
    Nothing -> tacticError $ GoalMismatch "apply_" g

-- | Tries to automatically solve a given goal.
auto :: Int -> Tactic Judgement ()
auto 0 = pure ()
auto n = do
  try forall
  try intros_
  try (split <|> assumption <|> apply_)
  auto (n - 1)
