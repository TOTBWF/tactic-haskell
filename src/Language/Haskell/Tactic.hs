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
  -- * Tactics
  , (<@>)
  , (?)
  , try
  , Evidence(..)
  , assumption
  , forall
  , intro
  , intro_
  , intros
  , intros_
  , apply_
  , split
  , induction
  , auto
  -- * Running Tactics
  , tactic
  -- * Re-Exports
  , Alt(..)
  ) where

import Control.Monad.Except

import Data.Foldable
import Data.Traversable
import Data.Function

import Language.Haskell.TH
import Language.Haskell.TH.Ppr hiding (split)
import Language.Haskell.TH.PprLib (Doc, (<+>), ($+$))
import qualified Language.Haskell.TH.PprLib as P

import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import Language.Haskell.Tactic.Internal.TH
import Language.Haskell.Tactic.Internal.Tactic

class Evidence e where
  -- | When the hypothesis variable passed in matches the goal type,
  -- discharge the goal and create no new subgoals.
  exact :: e -> Tactic ()

  -- | When the hypothesis variable passed in refers to a function whose return type matches the goal,
  -- this tactic generates subgoals for all of the argument types.
  apply :: e -> Tactic ()

instance Evidence String where
  exact n = mkTactic $ \j@(Judgement hy g) ->
    case J.lookup n j of
      Just (e, t) -> if (t == g) then return e else throwError $ TypeMismatch g e t
      Nothing -> throwError $ UndefinedHypothesis n

  apply f = mkTactic $ \j@(Judgement hy g) ->
    case (J.lookup f j) of
      Just (e, (Function args ret)) | ret == g -> do
        foldl AppE e <$> traverse (subgoal . Judgement hy) args
      Just (_, t) -> throwError $ GoalMismatch "apply" t
      Nothing -> throwError $ UndefinedHypothesis f

instance Evidence Name where
  exact n = mkTactic $ \j@(Judgement hy g) -> do
    t <- lookupVarType n
    case (t == g) of
      True -> return (VarE n)
      False -> throwError $ TypeMismatch g (VarE n) t

  apply n = mkTactic $ \j@(Judgement hy g) ->
    lookupVarType n >>= \case
      (Function args ret) | ret == g -> do
        foldl AppE (ConE n) <$> traverse (subgoal . Judgement hy) args
      t -> throwError $ GoalMismatch "apply" t

-- | Searches the hypotheses, looking for one that matches the goal type.
assumption :: Tactic ()
assumption = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find ((== g) . snd) hy of
    Just (_,(e, _)) -> return e
    Nothing -> throwError $ GoalMismatch "assumption" g

-- | Used to discharge any @forall@ statements at the begining
-- of a polymorphic type signature. This will hopefully not exist
-- for too long. DO NOT APPLY TO RANKNTYPES!!!!
forall :: Tactic ()
forall = mkTactic $ \(Judgement hy g) ->
  case g of
    (ForallT _ _ t) -> do
      subgoal $ Judgement hy t
    t -> throwError $ GoalMismatch "forall" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, using the provided name, and generates
-- a subgoal of type @t@.
intro :: String -> Tactic ()
intro n = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      x <- unique n
      LamE [VarP x] <$> subgoal (Judgement (hy @> (n,(VarE x, a))) b)
      -- return $ \[body] -> LamE [VarP x] body
    t -> throwError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, and generates
-- a subgoal of type @t@.
intro_ :: Tactic  ()
intro_ = mkTactic $ \(Judgement hy g) ->
  case g of
    (Arrow a b) -> do
      (n, x) <- fresh "x"
      LamE [VarP x] <$> subgoal (Judgement (hy @> (n, (VarE x, a))) b)
    t -> throwError $ GoalMismatch "intro_" t

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


-- | Looks through the context, trying to find a function that could potentially be applied.
apply_ :: Tactic ()
apply_ = mkTactic $ \j@(Judgement hy g) ->
  case Tl.find (\case (_, Function args ret) -> ret == g; _ -> False) hy of
    Just (_, (f, Function args ret)) -> do
      foldl AppE f <$> traverse (subgoal . Judgement hy) args
    Nothing -> throwError $ GoalMismatch "apply_" g

-- | The induction tactic works on inductive data types.
induction :: String -> Tactic ()
induction n = mkTactic $ \j@(Judgement hy goal) ->
  case (J.lookup n j) of
    Just (x, Constructor indn tvars) -> do
      ctrs <- lookupConstructors indn
      -- We need to check that any instances of recursion are
      -- replaced by the goal type...
      -- Furthermore, every time we use one of those "variables",
      -- we need to replace the usage with a recursive call?
      -- This means that we need to generate something like "fix"
      -- let genSubgoal = d
      (ffix, ffixn) <- fresh "f"
      (xfix, xfixn) <- fresh "x"
      matches <- for ctrs $ \(DCon cn tys) -> do
        -- Generate names for each of the parameters of the constructor
        ns <- traverse (const (fresh "ind")) tys
        -- Generate all of the pattern variables
        let pats = fmap (VarP . snd) ns
        -- If we see an instance of a recursive datatype, replace the type with the type of goal
        -- and the expression with a reference to the fix point
        let newHyps = zipWith (\(s, n) -> \case
                             Constructor tyn tv | tyn == indn -> (s, (AppE (VarE ffixn) (VarE n), goal))
                             t -> (s, (VarE n, t))) ns tys
        body <- subgoal (J.extends (Tl.fromList newHyps) $ J.remove n j)
        return $ Match (ConP cn pats) (NormalB body) []

      -- In order to get the recursive calls just right, we can use `fix`.
      return $ fixExp (LamE [VarP ffixn, VarP xfixn] (CaseE (VarE xfixn) matches)) x
    Just (_, t) -> throwError $ GoalMismatch "induction" t
    Nothing -> throwError $ UndefinedHypothesis n
  where


    fixExp :: Exp -> Exp -> Exp
    fixExp f a = AppE (AppE (VarE 'fix) f) a

-- | Tries to automatically solve a given goal.
auto :: Int -> Tactic ()
auto 0 = pure ()
auto n = do
  try forall
  try intros_
  try (split <!> assumption <!> apply_)
  auto (n - 1)
