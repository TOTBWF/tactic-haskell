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
module Language.Haskell.Tactic
  ( Tactic
  , runTactic
  -- * Tactics
  , Exact(..)
  , assumption
  , using
  , forall
  , intro
  , intro_
  , intros
  , intros_
  , Apply(..)
  , apply_
  , split
  -- , induction
  , auto
  -- ** Combinators
  , (<@>)
  , solve
  , try
  , many_
  , choice
  -- ** Subgoal Manipulation
  , goal
  , focus
  -- * Running Tactics
  -- , tactic
  -- , debugTactic
  -- * Re-Exports
  , Alt(..)
  ) where

import Control.Monad.Except

import Data.Foldable

import Bag
import DynFlags
import Name
import Id
import Outputable
import ErrUtils
import SrcLoc
import TcRnMonad
import TyCoRep
import Type

import Refinery.Tactic hiding (choice)
import qualified Refinery.Tactic as T

import qualified Language.Haskell.Tactic.Telescope as Tl
import Language.Haskell.Tactic.Telescope (Telescope, (@>))
import qualified Language.Haskell.Tactic.Judgement as J
import Language.Haskell.Tactic.Judgement (Judgement(..), Expr)
import Language.Haskell.Tactic.T
import Language.Haskell.Tactic.Patterns
import Language.Haskell.Tactic.Internal

type Tactic a = TacticT Judgement Expr T a

runTactic :: Type -> Tactic () -> TcM (Messages, Maybe Expr)
runTactic ty tac = do
  dflags <- getDynFlags
  (runT mempty $ T.runTacticT tac  $ J.empty ty) >>= \case
    Left err -> do
      let errMsg = mkErrMsg dflags noSrcSpan neverQualify (ppr err)
      return ((emptyBag, unitBag errMsg), Nothing)
    Right (ext, subgoals) -> do
      let errMsgs =
            if null subgoals
            then emptyBag
            else unitBag $ mkErrMsg dflags noSrcSpan neverQualify (ppr $ UnsolvedGoals subgoals)
      return ((emptyBag, errMsgs), Just ext)

class Exact e where
  -- | When the hypothesis variable passed in matches the goal type,
  -- discharge the goal and create no new subgoals.
  exact :: e -> Tactic ()

instance Exact String where
  exact n = rule $ \j@(Judgement _ g) ->
    case J.lookup n j of
      Just (e, t) -> do
        unify g t
        return e
      Nothing -> throwError $ UndefinedHypothesis n

instance Exact Name where
  exact n = rule $ \(Judgement _ g) -> do
    (e, t) <- lookupVarType n
    case (t `eqType` g) of
      True -> return e
      False -> throwError $ TypeMismatch g e t

-- instance Exact Integer where
--   exact i = rule $ \(Judgement _ g) -> implements g ''Num >>= \case
--     True -> return $ AppE (VarE 'fromInteger) (LitE $ IntegerL i)
--     False -> throwError $ GoalMismatch "exact" g

-- | Bring an outside value into the context
using :: Name -> Tactic ()
using n = rule $ \(Judgement hy g) -> do
  (e, t) <- lookupVarType n
  subgoal $ Judgement (hy @> (nameStableString n, (e, t))) g


-- | Searches the hypotheses, looking for one that matches the goal type.
assumption :: Tactic ()
assumption = rule $ \(Judgement hy g) ->
  case Tl.find ((eqType g) . snd) hy of
    Just (_,(e, _)) -> return e
    Nothing -> throwError $ GoalMismatch "assumption" g

-- | Used to discharge any @forall@ statements at the begining
-- of a polymorphic type signature. This will hopefully not exist
-- for too long. DO NOT APPLY TO RANKNTYPES!!!!
forall :: Tactic ()
forall = rule $ \(Judgement hy g) ->
  case g of
    (ForAllTy _ t) -> do
      subgoal $ Judgement hy t
    t -> throwError $ GoalMismatch "forall" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, using the provided name, and generates
-- a subgoal of type @t@.
intro :: String -> Tactic ()
intro n = rule $ \(Judgement hy g) ->
  case g of
    (FunTy a b) -> do
      x <- unique n
      let v = mkLocalId x a
      lam v a b <$> subgoal (Judgement (hy @> (n, (var v, a))) b)
    t -> throwError $ GoalMismatch "intro" t

-- | Applies to goals of the form @a -> b@.
-- Brings @a@ in as a hypothesis, and generates
-- a subgoal of type @t@.
intro_ :: Tactic  ()
intro_ = rule $ \(Judgement hy g) ->
  case g of
    (FunTy a b) -> do
      (n, x) <- fresh "x"
      let v = mkLocalId x a
      lam v a b <$> subgoal (Judgement (hy @> (n, (var v, a))) b)
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
split = rule $ \(Judgement hy g) ->
  case g of
    (Tuple ts) -> do
      tuple <$> traverse (subgoal . Judgement hy) ts
    t -> throwError $ GoalMismatch "tuple" t

class Apply e where
  -- | When the hypothesis variable passed in refers to a function whose return type matches the goal,
  -- this tactic generates subgoals for all of the argument types.
  apply :: e -> Tactic ()

instance Apply String where
  apply f = rule $ \j@(Judgement hy g) ->
    case (J.lookup f j) of
      Just (e, (Function args ret)) -> do
        unify ret g
        -- Need to unify ret + g. Furthermore, each subgoal may be dependent on the unification results
        -- of the others...
        foldl app e <$> traverse (subgoal . Judgement hy) args
      Just (_, t) -> throwError $ GoalMismatch "apply" t
      Nothing -> throwError $ UndefinedHypothesis f

instance Apply Name where
  apply n = rule $ \(Judgement hy g) ->
    lookupVarType n >>= \case
      (x, Function args ret) | ret `eqType` g -> do
        foldl app x <$> traverse (subgoal . Judgement hy) args
      (_, t) -> throwError $ GoalMismatch "apply" t

-- | Looks through the context, trying to find a function that could potentially be applied.
apply_ :: Tactic ()
apply_ = rule $ \(Judgement hy g) ->
  case Tl.find (\case (_, Function _ ret) -> ret `eqType` g; _ -> False) hy of
    Just (_, (f, Function args _)) -> do
      foldl app f <$> traverse (subgoal . Judgement hy) args
    _ -> throwError $ GoalMismatch "apply_" g


-- -- | The induction tactic works on inductive data types.
-- induction :: String -> Tactic ()
-- induction n = rule $ \j@(Judgement _ goal) ->
--   case (J.lookup n j) of
--     Just (x, Constructor indn tvars) -> do
--       ctrs <- lookupConstructors indn tvars
--       -- Because this can be used inside of something like an apply,
--       -- we need to use "fix"
--       (_, ffixn) <- fresh "ffix"
--       (_, xfixn) <- fresh "x"
--       matches <- for ctrs $ \(DCon cn tys) -> do
--         -- Generate names for each of the parameters of the constructor
--         ns <- traverse (const (fresh "ind")) tys
--         -- Generate all of the pattern variables
--         let pats = fmap (VarP . snd) ns
--         -- If we see an instance of a recursive datatype, replace the type with the type of goal -- and the expression with a reference to the fix point
--         let newHyps = zipWith (\(s, n) -> \case
--                              Constructor tyn _ | tyn == indn -> (s, (AppE (VarE ffixn) (VarE n), goal))
--                              t -> (s, (VarE n, t))) ns tys
--         body <- subgoal (J.extends (Tl.fromList newHyps) $ J.remove n j)
--         return $ Match (ConP cn pats) (NormalB body) []
--       return $ fixExp (LamE [VarP ffixn, VarP xfixn] (CaseE (VarE xfixn) matches)) x
--     Just (_, t) -> throwError $ GoalMismatch "induction" t
--     Nothing -> throwError $ UndefinedHypothesis n
--   where
--     fixExp :: Expr -> Expr -> Expr
--     fixExp f a = AppE (AppE (VarE 'fix) f) a

-- | @choice ts@ tries to apply a series of tactics @ts@, and commits to the
-- 1st tactic that succeeds. If they all fail, then @NoApplicableTactic@ is thrown
choice :: [Tactic ()] -> Tactic ()
choice [] = goal >>= (throwError . NoApplicableTactic)
choice (t:ts) = t <!> choice ts
-- choice = T.choice NoApplicableTactic
-- | @solve t@ runs the tactic @t@, and fails with @NoProgress@ if there are subgoals
-- remaining
solve :: Tactic () -> Tactic ()
solve t = t >> throwError NoProgress

-- | Tries to automatically solve a given goal.
auto :: Int -> Tactic ()
auto 0 = pure ()
auto n = do
  many_ forall
  try intros_
  choice
    [ split >> auto (n - 1)
    , attemptOn apply matchingFns
    -- , attemptOn induction matchingCtrs
    , assumption >> auto (n - 1) -- This should come last to prevent any stupidity regarding folds/etc
    ]
  where
    attemptOn :: (String -> Tactic ()) -> (Judgement -> [String]) -> Tactic ()
    attemptOn ft fv = do
      j <- goal
      choice $ fmap (\s -> ft s >> solve (auto $ n - 1)) $ fv j
      -- match $ choice . fmap (\s -> ft s >> solve (auto (n - 1))) . fv

    getVars :: Telescope String (Expr, Type) -> (Type -> Bool) -> [String]
    getVars hys pred = fmap fst $ Tl.toList $ Tl.filter pred $ fmap snd hys

    matchingFns :: Judgement -> [String]
    matchingFns (Judgement hys t) = getVars hys $ \case
      (Function _ ret) -> ret `eqType` t
      _ -> False

    matchingCtrs :: Judgement -> [String]
    matchingCtrs (Judgement hys _) = getVars hys $ \case
      (Constructor _ _) -> True
      _ -> False
