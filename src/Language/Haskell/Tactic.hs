{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.Tactic
  ( Tactic
  , (<..>)
  , exact
  , forall
  , intro
  , split
  , apply
  , tactic
  ) where

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

-- intro_ :: Tactic Judgement ()
-- intro_ = mkTactic $ \(Judgement hy g) ->
--   case g of
--     (Arrow a b) -> do
--       v <- define_ a
--       subgoal (Judgement (hy @> ("x",v)) b)
--       return $ \[body] -> LamE [VarP $ varName v] body

-- | Used to discharge any @forall@ statements at the begining
-- of a polymorphic type signature. This will hopefully not exist
-- for too long. DO NOT APPLY TO RANKNTYPES!!!!
forall :: Tactic Judgement ()
forall = mkTactic $ \(Judgement hy g) ->
  case g of
    (ForallT _ _ t) -> do
      subgoal $ Judgement hy t
      return $ head

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
