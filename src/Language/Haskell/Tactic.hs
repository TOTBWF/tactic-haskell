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
  , Exact(..)
  , assumption
  , forall
  , intro
  , intro_
  , intros
  , intros_
  , Apply(..)
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

import Language.Haskell.TH hiding (match)

import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.Telescope ((@>))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import Language.Haskell.Tactic.Internal.TH
import Language.Haskell.Tactic.Internal.Tactic

class Exact e where
  -- | When the hypothesis variable passed in matches the goal type,
  -- discharge the goal and create no new subgoals.
  exact :: e -> Tactic ()

instance Exact String where
  exact n = mkTactic $ \j@(Judgement _ g) ->
    case J.lookup n j of
      Just (e, t) -> if (t == g) then return e else throwError $ TypeMismatch g e t
      Nothing -> throwError $ UndefinedHypothesis n

instance Exact Name where
  exact n = mkTactic $ \(Judgement _ g) -> do
    (e, t) <- lookupVarType n
    case (t == g) of
      True -> return e
      False -> throwError $ TypeMismatch g e t

instance Exact Integer where
  exact i = mkTactic $ \(Judgement _ g) -> implements g ''Num >>= \case
    True -> return $ AppE (VarE 'fromInteger) (LitE $ IntegerL i)
    False -> throwError $ GoalMismatch "exact" g

-- | Searches the hypotheses, looking for one that matches the goal type.
assumption :: Tactic ()
assumption = mkTactic $ \(Judgement hy g) ->
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

class Apply e where
  -- | When the hypothesis variable passed in refers to a function whose return type matches the goal,
  -- this tactic generates subgoals for all of the argument types.
  apply :: e -> Tactic ()

instance Apply String where
  apply f = mkTactic $ \j@(Judgement hy g) ->
    case (J.lookup f j) of
      Just (e, (Function args ret)) | ret == g -> do
        foldl AppE e <$> traverse (subgoal . Judgement hy) args
      Just (_, t) -> throwError $ GoalMismatch "apply" t
      Nothing -> throwError $ UndefinedHypothesis f

instance Apply Name where
  apply n = mkTactic $ \(Judgement hy g) ->
    lookupVarType n >>= \case
      (x, Function args ret) | ret == g -> do
        foldl AppE x <$> traverse (subgoal . Judgement hy) args
      (_, t) -> throwError $ GoalMismatch "apply" t

-- | Looks through the context, trying to find a function that could potentially be applied.
apply_ :: Tactic ()
apply_ = mkTactic $ \(Judgement hy g) ->
  case Tl.find (\case (_, Function _ ret) -> ret == g; _ -> False) hy of
    Just (_, (f, Function args _)) -> do
      foldl AppE f <$> traverse (subgoal . Judgement hy) args
    _ -> throwError $ GoalMismatch "apply_" g

-- | The induction tactic works on inductive data types.
induction :: String -> Tactic ()
induction n = mkTactic $ \j@(Judgement _ goal) ->
  case (J.lookup n j) of
    Just (x, Constructor indn tvars) -> do
      ctrs <- lookupConstructors indn tvars
      -- Because this can be used inside of something like an apply,
      -- we need to use "fix"
      (_, ffixn) <- fresh "ffix"
      (_, xfixn) <- fresh "x"
      matches <- for ctrs $ \(DCon cn tys) -> do
        -- Generate names for each of the parameters of the constructor
        ns <- traverse (const (fresh "ind")) tys
        -- Generate all of the pattern variables
        let pats = fmap (VarP . snd) ns
        -- If we see an instance of a recursive datatype, replace the type with the type of goal -- and the expression with a reference to the fix point
        let newHyps = zipWith (\(s, n) -> \case
                             Constructor tyn _ | tyn == indn -> (s, (AppE (VarE ffixn) (VarE n), goal))
                             t -> (s, (VarE n, t))) ns tys
        body <- subgoal (J.extends (Tl.fromList newHyps) $ J.remove n j)
        return $ Match (ConP cn pats) (NormalB body) []

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
  choice
    [ split >> auto (n - 1)
    , assumption >> auto (n - 1)
    , match $ choice . fmap (\s -> apply s >> progress (auto (n - 1)) ) . matchingFns
    ]
  where
    matchingFns :: Judgement -> [String]
    matchingFns (Judgement hys t) = fmap fst $ Tl.toList $ flip Tl.filter hys $ \case
      (_, Function _ ret) -> ret == t
      _ -> False
