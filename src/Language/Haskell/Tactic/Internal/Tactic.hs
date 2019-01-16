-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = Tactics
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.Tactic.Internal.Tactic
  ( Tactic
  , (<..>)
  , TacticM
  , mkTactic
  , subgoal
  , fresh
  -- , define_
  , TacticError(..)
  , tacticError
  , tactic
  ) where
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Fail (MonadFail)

import Data.Foldable
import Data.Maybe
import Data.Bifunctor
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Text.PrettyPrint as P (render)
import Language.Haskell.TH
import Language.Haskell.TH.Ppr hiding (split)
import Language.Haskell.TH.PprLib (Doc, (<+>), ($+$))
import qualified Language.Haskell.TH.PprLib as P

import Data.Traversable.Extensions

import Language.Haskell.Tactic.Internal.T
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Telescope (Telescope, (@>))
import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.ProofState

-- | A @'Tactic'@ is simply a function from a 'jdg' to a @'ProofState'@.
-- However, we add an extra parameter 'a' so that @'Tactic'@ can become a @'Monad'@.
newtype Tactic jdg a = Tactic { runTactic :: jdg -> T (ProofState (a, jdg))  }

type MultiTactic jdg a = Tactic (ProofState jdg) a

instance Functor (Tactic jdg) where
  fmap f t = Tactic $ \j -> fmap (fmap (first f)) $ runTactic t $ j

instance Applicative (Tactic jdg) where
  pure a = Tactic $ \j -> pure (pure (a, j))
  (<*>) = ap

instance Monad (Tactic jdg) where
  return = pure
  t >>= k = Tactic $ \j -> do
    ps <- runTactic t $ j
    join <$> traverse (\(a, j') -> runTactic (k a) $ j') ps

instance Alternative (Tactic jdg) where
  empty = Tactic $ \_ -> empty
  (Tactic t1) <|> (Tactic t2) = Tactic $ \j -> (t1 j) <|> (t2 j)

runTactic_ :: Tactic jdg () -> jdg -> T (ProofState jdg)
runTactic_ t j = fmap snd <$> (runTactic t j)

each :: [Tactic jdg ()] -> MultiTactic jdg ()
each ts = Tactic $ fmap (fmap ((),) . snd) . mapAccumLM applyTac ts
  where
    applyTac (t:ts) j = ((ts,) . fmap snd) <$> (runTactic t) j
    applyTac [] j            = (([],) . fmap snd) <$> (runTactic $ pure ()) j

-- | @t '<..>' ts@ applies the tactic @t@, then applies each of the 'ts' to
-- the resulting subgoals
(<..>) :: Tactic jdg () -> [Tactic jdg ()] -> Tactic jdg ()
t <..> ts = Tactic $ \j -> (fmap ((),) . join) <$> (runTactic_ (each ts) =<< runTactic_ t j)

-- | State for the @'Tactic'@ construction helper.
data TacticState = TacticState
  { subgoals :: [Judgement]
  , hypothesisVars :: Set String
  }

-- Need to be careful about how this works...
-- When taking the names from mkTactic, we obtain the nameBase.
--

addVar :: String -> StateT TacticState T Name
addVar nm = do
  modify (\s -> s { hypothesisVars = Set.insert nm $ hypothesisVars s })
  lift $ T $ newName nm

-- | Tactic creation monad.
newtype TacticM a = TacticM { unTacticM :: (StateT TacticState T) a }
  deriving (Functor, Applicative, Monad, MonadFail)

-- | Creates a @'Tactic'@. See @'subgoal'@ and @'define'@ for the rest of the tactic creation API.
mkTactic :: (Judgement -> TacticM ([Exp] -> Exp)) -> Tactic Judgement ()
mkTactic t = Tactic $ \j@(Judgement hyps _) -> do
  (ext, s) <- runStateT (unTacticM $ t j) (TacticState [] (Set.fromList $ fmap (nameBase . fst) $ Tl.toList hyps))
  pure $ ProofState (reverse $ zip (repeat ()) $ subgoals s) ext

-- | Creates a new subgoal.
subgoal :: Judgement -> TacticM ()
subgoal j = TacticM $ modify (\s -> s { subgoals = j:subgoals s })

-- | Defines a new hypothesis variable with a given name.
fresh :: String -> TacticM Name
fresh "" = tacticError $ InvalidHypothesisName "\"\""
fresh nm = TacticM $ gets (isDefined nm . hypothesisVars) >>= \case
  True -> tacticError $ DuplicateHypothesis nm
  False -> addVar nm
  where
    isDefined :: String -> Set String -> Bool
    isDefined nm s = (head nm == '_') || (Set.member nm s)

-- wildcard :: TacticM Name
-- wildcard = _h

{- Error Handling -}
render :: Doc -> String
render = P.render . P.to_HPJ_Doc

data TacticError
  = TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UndefinedHypothesis String
  | DuplicateHypothesis String
  | InvalidHypothesisName String
  | UnsolvedGoals [Judgement]
  | NotImplemented String

-- | Throws a tactic error.
tacticError :: (MonadFail m) => TacticError -> m a
tacticError e =
  let errText = case e of
        TypeMismatch{ expectedType, expr, exprType } ->
          P.text "Expected Type" <+> ppr expectedType <+> P.text "but" <+> ppr expr <+> P.text "has type" <+> ppr exprType $+$
            P.text "Expected Type (Debug):" <+> (P.text $ show expectedType) $+$
            P.text "Actual Type (Debug):" <+> (P.text $ show exprType)
        GoalMismatch{ tacName, appliedGoal } ->
          P.text "Tactic" <+> P.text tacName <+> P.text "doesn't support goals of the form" <+> ppr appliedGoal $+$
            P.text "Debug:" <+> (P.text $ show appliedGoal)
        UndefinedHypothesis v ->
          P.text "Undefined Hypothesis" <+> P.text v
        DuplicateHypothesis v ->
          P.text "Duplicate Hypothesis" <+> P.text v
        InvalidHypothesisName v ->
          P.text "Invalid Hypothesis Name" <+> P.text v
        UnsolvedGoals subgoals ->
          P.text "Unsolved Subgoals" <+> P.vcat (fmap ppr subgoals)
        NotImplemented t -> P.text t <+> P.text "isn't implemented yet"
  in fail $ render $ P.text "Tactic Error:" <+> errText

-- | Runs a tactic script against a goal, and generates a @'Dec'@.
tactic :: String -> Q Type -> Tactic Judgement () -> Q [Dec]
tactic nm ty tac = do
  fnm <- newName nm
  (ProofState subgoals ext) <- runT $ fmap snd <$> (runTactic tac =<< (J.empty <$> T ty))
  case subgoals of
    [] -> return [ValD (VarP fnm) (NormalB $ ext []) []]
    _ -> tacticError $ UnsolvedGoals subgoals
