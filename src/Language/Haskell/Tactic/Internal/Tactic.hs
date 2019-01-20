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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Haskell.Tactic.Internal.Tactic
  ( Tactic
  -- , (<..>)
  -- , try
  -- , choice
  -- , TacticM
  -- , mkTactic
  -- , subgoal
  -- , fresh
  -- , wildcard
  -- , (?)
  -- , TacticError(..)
  -- , tacticError
  -- , tactic
  -- , printTac
  ) where

import Data.Functor.Alt
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Fail (MonadFail)
import Control.Monad.Morph

import Data.Bifunctor
-- import Data.Set (Set)
-- import qualified Data.Set as Set
import Pipes.Core
import Pipes.Lift

import qualified Text.PrettyPrint as P (render)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Ppr hiding (split)
import Language.Haskell.TH.PprLib (Doc, (<+>), ($+$))
import qualified Language.Haskell.TH.PprLib as P


import Language.Haskell.Tactic.Internal.T
import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.Telescope (Telescope, (@>))
import qualified Language.Haskell.Tactic.Internal.Telescope as Tl
import Language.Haskell.Tactic.Internal.ProofState

-- | A @'Tactic'@ is simply a function from a 'Judgement' to a @'ProofState'@.
-- However, we add an extra parameter 'a' so that @'Tactic'@ can become a @'Monad'@.
newtype Tactic a = Tactic { unTactic :: StateT Judgement (ProofStateT T) a  }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

runTactic :: Tactic () -> Judgement -> T (Exp, [Judgement])
runTactic (Tactic t) j =
  fmap (second reverse)
  $ flip runStateT []
  $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t j)
  where
    server :: jdg -> Server jdg Exp (StateT [jdg] T) Exp
    server j = do
      modify (j:)
      hole <- lift $ lift $ qNewName "_"
      respond (UnboundVarE hole) >>= server

-- try :: Tactic () -> Tactic ()
-- try t = t <!> (pure ())

-- choice :: (Judgement -> Tactic Judgement ()) -> Tactic Judgement ()
-- choice c = Tactic $ \j -> runTactic (c j) j

-- -- We need to be able to match on the goal type...
-- --

-- -- | @t '<..>' ts@ applies the tactic @t@, then applies each of the 'ts' to
-- -- the resulting subgoals
-- (<..>) :: Tactic jdg () -> [Tactic jdg ()] -> Tactic jdg ()
-- t <..> ts = Tactic $ \j -> (fmap ((),) . join) <$> (runTactic_ (each ts) =<< runTactic_ t j)

-- -- | State for the @'Tactic'@ construction helper.
-- data TacticState = TacticState
--   { subgoals :: [Judgement]
--   , hypothesisVars :: Set String
--   }

-- addVar :: String -> StateT TacticState T Name
-- addVar nm = do
--   modify (\s -> s { hypothesisVars = Set.insert nm $ hypothesisVars s })
--   lift $ T $ newName nm

-- -- | Tactic creation monad.
-- newtype TacticM a = TacticM { unTacticM :: (StateT TacticState T) a }
--   deriving (Functor, Applicative, Monad, MonadFail)

-- liftT :: T a -> TacticM a
-- liftT t = TacticM $ StateT $ \s -> (,s) <$> t

-- -- | Creates a @'Tactic'@. See @'subgoal'@ and @'define'@ for the rest of the tactic creation API.
-- mkTactic :: (Judgement -> TacticM ([Exp] -> Exp)) -> Tactic Judgement ()
-- mkTactic t = Tactic $ \j@(Judgement hyps _) -> do
--   (ext, s) <- runStateT (unTacticM $ t j) (TacticState [] (Set.fromList $ fmap (nameBase . fst) $ Tl.toList hyps))
--   pure $ ProofState (reverse $ zip (repeat ()) $ subgoals s) ext

-- -- | Creates a new subgoal.
-- subgoal :: Judgement -> TacticM ()
-- subgoal j = TacticM $ modify (\s -> s { subgoals = j:subgoals s })

-- -- | Defines a new hypothesis variable with a given name.
-- fresh :: String -> TacticM Name
-- fresh "" = tacticError $ InvalidHypothesisName "\"\""
-- fresh nm = TacticM $ gets (isDefined nm . hypothesisVars) >>= \case
--   True -> tacticError $ DuplicateHypothesis nm
--   False -> addVar nm
--   where
--     isDefined :: String -> Set String -> Bool
--     isDefined nm s = (head nm == '_') || (Set.member nm s)

-- -- | Defines a wildcard hypothesis variable.
-- wildcard :: TacticM Name
-- wildcard = TacticM $ do
--   -- The way this works is pretty hacky...
--   c <- gets (Set.size . Set.filter ((== '_') . head ) . hypothesisVars)
--   addVar ("_" ++ show c)

-- {- Error Handling -}
-- render :: Doc -> String
-- render = P.render . P.to_HPJ_Doc

-- data TacticError
--   = TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
--   | GoalMismatch { tacName :: String, appliedGoal :: Type }
--   | UndefinedHypothesis String
--   | DuplicateHypothesis String
--   | InvalidHypothesisName String
--   | UnsolvedGoals (ProofState Judgement)
--   | NotImplemented String

-- -- | Throws a tactic error.
-- tacticError :: (MonadFail m) => TacticError -> m a
-- tacticError e =
--   let errText = case e of
--         TypeMismatch{ expectedType, expr, exprType } ->
--           P.text "Expected Type" <+> ppr expectedType <+> P.text "but" <+> ppr expr <+> P.text "has type" <+> ppr exprType $+$
--             P.text "Expected Type (Debug):" <+> (P.text $ show expectedType) $+$
--             P.text "Actual Type (Debug):" <+> (P.text $ show exprType)
--         GoalMismatch{ tacName, appliedGoal } ->
--           P.text "Tactic" <+> P.text tacName <+> P.text "doesn't support goals of the form" <+> ppr appliedGoal $+$
--             P.text "Debug:" <+> (P.text $ show appliedGoal)
--         UndefinedHypothesis v ->
--           P.text "Undefined Hypothesis" <+> P.text v
--         DuplicateHypothesis v ->
--           P.text "Duplicate Hypothesis" <+> P.text v
--         InvalidHypothesisName v ->
--           P.text "Invalid Hypothesis Name" <+> P.text v
--         UnsolvedGoals ps ->
--           P.text "Unsolved Subgoals" $+$ ppr ps
--         NotImplemented t -> P.text t <+> P.text "isn't implemented yet"
--   in fail $ render $ P.text "Tactic Error:" <+> errText

-- tacticPrint :: String -> TacticM ()
-- tacticPrint = liftT . T . reportWarning

-- -- | Prints out the proof state after the provided tactic was executed.
-- (?) :: Tactic Judgement () -> String -> Tactic Judgement ()
-- t ? lbl = Tactic $ \j -> do
--   ps <- runTactic t j
--   T $ reportWarning $ render $ P.text "Proof State" <+> P.parens (P.text lbl) $+$ ppr (fmap snd ps)
--   return ps

-- -- | Runs a tactic script against a goal, and generates a @'Dec'@.
-- tactic :: String -> Q Type -> Tactic Judgement () -> Q [Dec]
-- tactic nm ty tac = do
--   fnm <- newName nm
--   p@(ProofState subgoals ext) <- runT $ fmap snd <$> (runTactic tac =<< (J.empty <$> T ty))
--   case subgoals of
--     [] -> return [ValD (VarP fnm) (NormalB $ ext []) []]
--     _ -> tacticError $ UnsolvedGoals p
