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
  , Alt(..)
  , (<@>)
  , try
  -- , choice
  -- , TacticM
  -- , mkTactic
  -- , subgoal
  -- , fresh
  -- , wildcard
  , subgoal
  , (?)
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
newtype Tactic a = Tactic { unTactic :: StateT Judgement (ProofStateT (ExceptT TacticError T)) a  }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance Alt (Tactic) where
  (Tactic t1) <!> (Tactic t2) = Tactic $ StateT $ \j -> (runStateT t1 j) <!> (runStateT t2 j)

try :: Tactic () -> Tactic ()
try t = t <!> (pure ())

(<@>) :: Tactic () -> [Tactic ()] -> Tactic ()
(Tactic t) <@> ts = Tactic $ StateT $ \j ->
  ProofStateT $ flip evalStateT (ts ++ repeat (pure ())) $ distribute $ applyTac >\\ (hoist lift $ unProofStateT $ runStateT t j)
  where
    applyTac :: ((), Judgement) -> Client ((), Judgement) Exp (StateT [Tactic ()] (ExceptT TacticError T)) Exp
    applyTac (_, j) = do
      t <- gets (unTactic . head)
      modify tail
      hoist lift $ unProofStateT $ runStateT t j

runTactic :: Tactic () -> Judgement -> T (Exp, [Judgement])
runTactic (Tactic t) j = do
  r <- runExceptT $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t j)
  case r of
    Left err -> hoistError err
    Right res -> return res
  where
    server :: jdg -> Server jdg Exp (StateT [jdg] (ExceptT TacticError T)) Exp
    server j = do
      modify (j:)
      hole <- lift $ lift $ lift $ qNewName "_"
      respond (UnboundVarE hole) >>= server



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

{- Error Handling -}

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

warning :: Doc -> ProofStateT (ExceptT TacticError T) ()
warning d = lift $ lift $ qReport False $ render d

subgoal :: Judgement -> ProofStateT (ExceptT TacticError T) ((), Judgement)
subgoal j = ProofStateT $ do
  request ((), j)

-- | Prints out the proof state after the provided tactic was executed.
(?) :: Tactic () -> String -> Tactic ()
(Tactic t) ? lbl = Tactic $ StateT $ \j -> do
  warning $ P.text "Proof State" <+> P.parens (P.text lbl)
  ((), j') <- runStateT t j
  warning $ ppr j'
  subgoal j'

-- -- | Runs a tactic script against a goal, and generates a @'Dec'@.
-- tactic :: String -> Q Type -> Tactic Judgement () -> Q [Dec]
-- tactic nm ty tac = do
--   fnm <- newName nm
--   p@(ProofState subgoals ext) <- runT $ fmap snd <$> (runTactic tac =<< (J.empty <$> T ty))
--   case subgoals of
--     [] -> return [ValD (VarP fnm) (NormalB $ ext []) []]
--     _ -> tacticError $ UnsolvedGoals p
