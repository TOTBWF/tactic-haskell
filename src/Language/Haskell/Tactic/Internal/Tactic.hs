-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = Tactics
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Haskell.Tactic.Internal.Tactic
  ( Tactic
  , TacticError(..)
  -- * Built-ins
  , (<@>)
  , (?)
  , try
  -- * Tactic Construction
  , Tac
  , mkTactic
  , subgoal
  -- ** Name Management
  , fresh
  , wildcard
  -- * Running Tactics
  , tactic
  -- * Re-Exports
  , Alt(..)
  ) where

import Data.Functor.Alt
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Fail (MonadFail)
import Control.Monad.Morph

import Data.Bifunctor
import Data.Set (Set)
import qualified Data.Set as Set

import Pipes.Core
import Pipes.Lift
import qualified Text.PrettyPrint as P (render)
import Language.Haskell.TH
import Language.Haskell.TH.Ppr hiding (split)
import Language.Haskell.TH.PprLib (Doc, (<+>), ($+$), ($$))
import qualified Language.Haskell.TH.PprLib as P


import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Telescope (Telescope, (@>))
import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.ProofState

-- | A @'Tactic'@ is simply a function from a 'Judgement' to a @'ProofState'@.
-- However, we add an extra parameter 'a' so that @'Tactic'@ can become a @'Monad'@.
newtype Tactic a = Tactic { unTactic :: StateT TacticState (ProofStateT (ExceptT TacticError Q)) a  }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadError TacticError)


data TacticState = TacticState
  { goal :: Judgement
  , boundVars :: Set String
  }

instance Alt (Tactic) where (Tactic t1) <!> (Tactic t2) = Tactic $ StateT $ \j -> (runStateT t1 j) <!> (runStateT t2 j)

-- | Tries to apply a tactic, and backtracks if the tactic fails.
try :: Tactic () -> Tactic ()
try t = t <!> (pure ())

-- | @t \<\@> ts@ Applies the tactic @t@, then applies each of the tactics in the list to one of the resulting subgoals.
-- If @ts@ is shorter than the list of resulting subgoals, the identity tactic will be applied to the remainder.
(<@>) :: Tactic () -> [Tactic ()] -> Tactic ()
(Tactic t) <@> ts = Tactic $ StateT $ \s -> ProofStateT $
  flip evalStateT (ts ++ repeat (pure ())) $ distribute $ applyTac >\\ (hoist lift $ unProofStateT $ runStateT t s)
  where
    applyTac :: ((), TacticState) -> Client ((), TacticState) Exp (StateT [Tactic ()] (ExceptT TacticError Q)) Exp
    applyTac (_, s) = do
      t <- gets (unTactic . head)
      modify tail
      hoist lift $ unProofStateT $ runStateT t s

-- | @t ? lbl@ traces out the proof state after applying @t@, annotated with the label @lbl@.
(?) :: Tactic () -> String -> Tactic ()
(Tactic t) ? lbl = Tactic $ StateT $ \j -> ProofStateT $ do
  (e, sg) <- flip runStateT [] $ distribute $ collectSubgoals >\\ (hoist lift $ unProofStateT $ runStateT t j)
  let warning = P.text "Proof State" <+> P.parens (P.text lbl) $+$ P.nest 4 (P.vcat (fmap pGoal $ zip [1..] (reverse sg)))
  lift $ lift $ reportWarning $ render warning
  return e
  where
    collectSubgoals :: ((), TacticState) -> Client ((), TacticState) Exp (StateT [Judgement] (ExceptT TacticError Q)) Exp
    collectSubgoals (_, s) = do
      modify (goal s:)
      request ((), s)

    pGoal :: (Int, Judgement) -> Doc
    pGoal (i, j) = P.text "#" P.<> P.int i $+$ P.nest 2 (ppr j $+$ P.text "")

runTactic :: Tactic () -> Judgement -> Q (Exp, [Judgement])
runTactic (Tactic t) j = do
  r <- runExceptT $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t $ TacticState j Set.empty)
  case r of
    Left err -> hoistError err
    Right (e, st) -> return $ (e, reverse $ fmap goal st)
  where
    server :: jdg -> Server jdg Exp (StateT [jdg] (ExceptT TacticError Q)) Exp
    server j = do
      modify (j:)
      hole <- lift $ lift $ lift $ newName "_"
      respond (UnboundVarE hole) >>= server

type Tac a  = StateT TacticState (Client TacticState Exp (ExceptT TacticError Q)) a


-- | Creates a @'Tactic'@. See @'subgoal'@ for the rest of the API.
mkTactic :: (Judgement -> Tac Exp) -> Tactic ()
mkTactic f = Tactic $ do
  j <- gets (goal)
  StateT $ \s -> ProofStateT $ do
     (e, s') <- (\s -> request ((), s)) >\\ runStateT (f (goal s)) s
     return e

-- | Creates a subgoal, and returns the extract.
subgoal :: Judgement -> Tac Exp
subgoal j = do
  s <- get
  lift $ request (s { goal = j })

liftQ :: Q a -> Tac a
liftQ = lift . lift . lift

bindVar :: String -> Tac Name
bindVar nm = do
  modify (\s -> s { boundVars = Set.insert nm $ boundVars s })
  liftQ $ newName nm

-- | Tries to create a name, and fails with @'DuplicateHypothesis'@ if the name is already taken.
-- Furthermore, names that begin with '_' are reserved for wildcard names.
fresh :: String -> Tac Name
fresh "" = throwError $ InvalidHypothesisName "\"\""
fresh nm = gets (isDefined nm . boundVars) >>= \case
  True -> throwError $ DuplicateHypothesis nm
  False -> bindVar nm
  where
    isDefined :: String -> Set String -> Bool
    isDefined nm s = (head nm == '_') || (Set.member nm s)


-- | Creates a fresh wildcard name.
wildcard :: Tac Name
wildcard = do
  -- The way this works is pretty hacky...
  c <- gets (Set.size . Set.filter ((== '_') . head) . boundVars)
  bindVar ("_" ++ show c)


data TacticError
  = TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UndefinedHypothesis String
  | DuplicateHypothesis String
  | InvalidHypothesisName String
  | UnsolvedGoals [Judgement]
  | NotImplemented String

render :: Doc -> String
render = P.render . P.to_HPJ_Doc

hoistError :: (MonadFail m) => TacticError -> m a
hoistError e =
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
        UnsolvedGoals ps ->
          P.text "Unsolved Subgoals" $+$ ppr ps
        NotImplemented t -> P.text t <+> P.text "isn't implemented yet"
  in fail $ render $ P.text "Tactic Error:" <+> errText

-- | @'tactic' nm [t| ty |] tac@ creates a declaration with the name @nm@ of type @ty@
-- by applying the tactic @tac@
tactic :: String -> Q Type -> Tactic () -> Q [Dec]
tactic nm qty tac = do
  decName <- newName nm
  ty <- qty
  (ext, subgoals) <- runTactic tac $ J.empty ty
  case subgoals of
    [] -> return [ValD (VarP decName) (NormalB $ ext) []]
    _ -> hoistError $ UnsolvedGoals subgoals
