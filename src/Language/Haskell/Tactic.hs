{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
module Language.Haskell.Tactic
  ( Tactic(..)
  , (<..>)
  , exact
  , intro_
  , intro
  , split
  , apply
  , tactic
  ) where

import Control.Monad.State.Strict
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fail (MonadFail)

import Data.Foldable
import Data.Bifunctor

import Data.String (IsString(..))

import Data.Traversable.Extensions

import qualified Text.PrettyPrint as P (render)

import Language.Haskell.TH
import Language.Haskell.TH.Ppr hiding (split)
import Language.Haskell.TH.PprLib (Doc)
import qualified Language.Haskell.TH.PprLib as P
import Language.Haskell.TH.Syntax hiding (lift)

import Language.Haskell.Tactic.ProofState
import Language.Haskell.Tactic.MetaSubst
import Language.Haskell.Tactic.Telescope (Telescope(..))
import qualified Language.Haskell.Tactic.Telescope as Tl
import Language.Haskell.Tactic.TH

newtype Tactic ext jdg m a = Tactic { runTactic :: jdg -> m (ProofState ext (a, jdg))  }
type MultiTactic ext jdg m a = Tactic ext (ProofState ext jdg) m a

runTactic_ :: (Monad m) => Tactic ext jdg m () -> jdg -> m (ProofState ext jdg)
runTactic_ t j = fmap snd <$> (runTactic t j)

instance (Functor m) => Functor (Tactic ext jdg m) where
  fmap f t = Tactic $ \j -> fmap (fmap (first f)) $ runTactic t $ j -- fmap (first (fmap f)) $ runTactic t $ j

instance (Monad m) => Applicative (Tactic ext jdg m) where
  pure a = Tactic $ \j -> pure (pure (a, j))
  (<*>) = ap

instance (Monad m) => Monad (Tactic ext jdg m) where
  return = pure
  t >>= k = Tactic $ \j -> do
    ps <- runTactic t $ j
    join <$> traverse (\(a, j') -> runTactic (k a) $ j') ps

instance (MonadPlus m) => Alternative (Tactic ext jdg m) where
  empty = Tactic $ \_ -> empty
  (Tactic t1) <|> (Tactic t2) = Tactic $ \j -> (t1 j) <|> (t2 j)

each :: (Monad m) => [Tactic ext jdg m ()] -> MultiTactic ext jdg m ()
each ts = Tactic $ fmap (fmap ((),) . snd) . mapAccumLM applyTac ts
  where
    applyTac (t:ts) j = ((ts,) . fmap snd) <$> (runTactic t) j
    applyTac [] j            = (([],) . fmap snd) <$> (runTactic $ pure ()) j

(<..>) :: (Monad m) => Tactic ext jdg m () -> [Tactic ext jdg m ()] -> Tactic ext jdg m ()
t <..> ts = Tactic $ \j -> (fmap ((),) . join) <$> (runTactic_ (each ts) =<< runTactic_ t j)

-- Some helpers for tactic construction
newtype TacticT ctx jdg m a = TacticT { unTacticT :: StateT [(ctx, jdg)] m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFail)

subgoal :: (Monad m) => ctx -> jdg -> TacticT ctx jdg m ()
subgoal c j = TacticT $ modify ((c,j):)

mkTactic :: (Monad m) => (jdg -> TacticT ctx jdg m ([ext] -> ext)) -> Tactic ext jdg m ctx
mkTactic t = Tactic $ \j -> do
  (ext, subgoals) <- runStateT (unTacticT $ t j) []
  pure $ ProofState (reverse subgoals) ext

-- Error handling/printing
render :: Doc -> String
render = P.render . P.to_HPJ_Doc

instance IsString Doc where
  fromString = P.text

data Error
  = TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UnsolvedGoals [Type]
  | NotImplemented String

tacticError :: (MonadFail m) => Error -> m a
tacticError e =
  let errText = case e of
        -- NoVariables -> "No variables to bring into scope"
        -- UndefinedVariable x -> "Undefined variable" P.<+> ppr x
        -- AssumptionError t -> "Couldn't find any variables of type" P.<+> ppr t
        TypeMismatch{..} ->
          "Expected Type" P.<+> ppr expectedType P.<+> "but" P.<+> ppr expr P.<+> "has type" P.<+> ppr exprType P.$+$
            "Expected Type (Debug):" P.<+> (P.text $ show expectedType) P.$+$
            "Actual Type (Debug):" P.<+> (P.text $ show exprType)
        GoalMismatch{..} ->
          "Tactic" P.<+> P.text tacName P.<+> "doesn't support goals of the form" P.<+> ppr appliedGoal P.$+$
            "Debug:" P.<+> (P.text $ show appliedGoal)
        UnsolvedGoals subgoals ->
          "Unsolved Subgoals" P.<+> P.vcat (fmap ppr subgoals)
        NotImplemented t -> P.text t P.<+> "isn't implemented yet"
  in fail $ render $ "Tactic Error:" P.<+> errText

data Var = Var Name Type

exact :: Var -> Tactic Exp Type Q ()
exact (Var x t) = mkTactic $ \g -> do
  if (t == g) then return (\_ -> VarE x) else tacticError $ TypeMismatch g (VarE x) t

intro_ :: Tactic Exp Type Q ()
intro_ = mkTactic $ \case
  (ForallT _ _ t) -> do
    subgoal () t
    return head
  t -> tacticError $ GoalMismatch "intro_" t

intro :: Tactic Exp Type Q Var
intro = mkTactic $ \case
  (Arrow a b) -> do
    x <- lift $ newName "x"
    subgoal (Var x a) b
    return $ \[body] -> LamE [VarP x] body
  t -> tacticError $ GoalMismatch "intro" t

split :: Tactic Exp Type Q ()
split = mkTactic $ \case
  (Tuple ts) -> do
    traverse_ (subgoal ()) ts
    return TupE
  t -> tacticError $ GoalMismatch "tuple" t

apply :: Var -> Tactic Exp Type Q ()
apply (Var f t) = mkTactic $ \g -> case t of
  (Function args ret) | ret == g -> do
    traverse_ (subgoal ()) args
    return $ foldl AppE (VarE f)
  t -> tacticError $ GoalMismatch "apply" t

tactic :: String -> Q Type -> Tactic Exp Type Q () -> Q [Dec]
tactic nm ty tac = do
  fnm <- newName nm
  (ProofState subgoals ext) <- fmap snd <$> (runTactic tac =<< ty)
  case subgoals of
    [] -> return [ValD (VarP fnm) (NormalB $ ext []) []]
    _ -> tacticError $ UnsolvedGoals subgoals
