-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = Tactics
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.Tactic.Internal.Tactic
  ( Tactic
  , TacticError(..)
  -- * Built-ins
  , (<@>)
  , match
  , (?)
  -- * Backtracking
  , try
  , choice
  , progress
  , solve
  -- * Tactic Construction
  , Tac
  , mkTactic
  , subgoal
  -- ** Name Management
  , unique
  , fresh
  -- ** Reify Wrappers
  , lookupConstructors
  , lookupVarType
  , implements
  -- ** Debugging helpers
  , debugPrint
  -- * Running Tactics
  , tactic
  , debugTactic
  -- * Re-Exports
  , Alt(..)
  ) where

import Data.Functor.Alt
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Fail (MonadFail)
import Control.Monad.Morph

import Data.Traversable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Pipes.Core
import Pipes.Lift
import qualified Text.PrettyPrint as P (render)
import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.PprLib (Doc, (<+>), ($+$))
import qualified Language.Haskell.TH.PprLib as P

import Language.Haskell.Tactic.Internal.Judgement (Judgement(..))
import qualified Language.Haskell.Tactic.Internal.Judgement as J
import Language.Haskell.Tactic.Internal.ProofState
import Language.Haskell.Tactic.Internal.TH

-- | A @'Tactic'@ is simply a function from a 'Judgement' to a @'ProofState'@.
-- However, we add an extra parameter 'a' so that @'Tactic'@ can become a @'Monad'@.
newtype Tactic a = Tactic { unTactic :: StateT TacticState (ProofStateT (ExceptT TacticError Q)) a  }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadError TacticError)


data TacticState = TacticState
  { goal :: Judgement
  , boundVars :: Map String Int
  }

instance Alt (Tactic) where (Tactic t1) <!> (Tactic t2) = Tactic $ StateT $ \j -> (runStateT t1 j) <!> (runStateT t2 j)

-- | @try t@ tries to apply a tactic @t@, and applies the identity tactic if
-- it fails.
try :: Tactic () -> Tactic ()
try t = t <!> (pure ())

-- | @choice ts@ tries to apply a series of tactics @ts@, and commits
-- to the 1st tactic that succeeds. If they all fail, then @NoApplicableTactic@
-- is thrown.
choice :: [Tactic ()] -> Tactic ()
choice [] = throwError NoApplicableTactic
choice (t:ts) = t <!> choice ts

-- | @progress t@ applies the tactic @t@, and throws a @NoProgress@ if
-- the resulting subgoals are all syntactically equal to the initial goal.
-- TODO: Use alpha-equality rather than literal equality. However,
-- That comes along with a big can of worms WRT type equality.
progress :: Tactic () -> Tactic ()
progress (Tactic t) = Tactic $ StateT $ \s -> do
  s' <- execStateT t s
  if (goal s' == goal s)
    then throwError NoProgress
    else return ((), s')

solve :: Tactic () -> Tactic ()
solve t = t >> throwError NoProgress

-- | @match f@ takes a function from a judgement to a @Tactic@, and
-- then applies the resulting @Tactic@.
match :: (Judgement -> Tactic ()) -> Tactic ()
match f = Tactic $ StateT $ \s -> runStateT (unTactic $ f $ goal s) s


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
  r <- runExceptT $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t $ TacticState j Map.empty)
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
mkTactic f = Tactic $ StateT $ \s -> ProofStateT $ (\s' -> request ((), s')) >\\ evalStateT (f $ goal s) s

-- | Creates a subgoal, and returns the extract.
subgoal :: Judgement -> Tac Exp
subgoal j = do
  s <- get
  lift $ request (s { goal = j })

liftQ :: Q a -> Tac a
liftQ = lift . lift . lift

-- | Tries to create a name, and fails with @'DuplicateHypothesis'@ if the name is already taken.
-- Furthermore, names that begin with '_' are reserved for wildcard names.
unique :: String -> Tac Name
unique "" = throwError $ InvalidHypothesisName "\"\""
unique n = gets (Map.member n . boundVars) >>= \case
  True -> throwError $ DuplicateHypothesis n
  False -> do
    modify (\s -> s { boundVars = Map.insert n 1 $ boundVars s })
    liftQ $ newName n
  -- where
  --   isDefined :: String -> Map String Int -> Bool
  --   isDefined nm s = (head nm == '_') || (Map.member nm s)

-- | Tries to create a name provided a base, potentially appending numbers to make it unique.
-- Furthermore, names that begin with '_' are reserved for wildcard names.
fresh :: String -> Tac (String, Name)
fresh "" = throwError $ InvalidHypothesisName "\"\""
fresh n = gets (Map.lookup n . boundVars) >>= \case
  Just i -> do
    modify (\s -> s { boundVars = Map.adjust (+ 1) n $ boundVars s })
    let n' = n ++ show i
    -- TODO: What happens if someone freshens something that ends
    (n', ) <$> (liftQ $ newName n')
  Nothing -> do
    modify (\s -> s { boundVars = Map.insert n 1 $ boundVars s })
    (n, ) <$> (liftQ $ newName n)

-- | Looks up a type's constructors.
lookupConstructors :: Name -> [Type] -> Tac ([DCon])
lookupConstructors n inst  = (liftQ $ reify n) >>= \case
  TyConI (DataD _ _ tvarBndrs _ cs _) -> do
    let instMap = Map.fromList $ zip (fmap (\case (PlainTV tn) -> tn; (KindedTV tn _) -> tn) tvarBndrs) inst
    let instantiate (_, t) = case t of
          VarT tv -> Map.findWithDefault t tv instMap
          _ -> t
    for cs $ \case
      NormalC cn ts -> return $ DCon cn $ fmap instantiate ts
      InfixC t1 cn t2 -> return $ DCon cn [instantiate t1, instantiate t2]
      c -> throwError $ NotImplemented $ "lookupConstructors: Constructors of form " ++ show c
  i -> throwError $ NotImplemented $ "lookupConstructors: Declarations of form " ++ show i

-- | Looks up the the type of a variable binding, along with
-- the expression form of the name
lookupVarType :: Name -> Tac (Exp, Type)
lookupVarType n = (liftQ $ reify n) >>= \case
  VarI _ t _ -> return (VarE n, t)
  DataConI _ t _ -> return (ConE n, t)
  i -> throwError $ NotImplemented $ "lookupVarType: Variable Type " ++ show i

-- | Check to see if a type implements a typeclass
implements :: Type -> Name -> Tac Bool
implements ty n = liftQ $ isInstance n [ty]

-- | Prints a debug message as a warning
debugPrint :: String -> Tac ()
debugPrint msg = liftQ $ reportWarning $ "DEBUG:" ++ msg

data TacticError
  = TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UndefinedHypothesis String
  | DuplicateHypothesis String
  | InvalidHypothesisName String
  | UnsolvedGoals [Judgement]
  | NoProgress
  | NoApplicableTactic
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
        NoProgress -> P.text "No Progress"
        NoApplicableTactic -> P.text "No Applicable Tactic"
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
    [] -> do
      return [ValD (VarP decName) (NormalB $ ext) []]
    _ -> hoistError $ UnsolvedGoals subgoals

-- | @debugTactic nm [t| ty |] tac@ behaves exactly the same as @tactic@,
-- but it prints out the resulting expression as a warning.
debugTactic :: String -> Q Type -> Tactic () -> Q [Dec]
debugTactic nm qty tac = do
  decName <- newName nm
  ty <- qty
  (ext, subgoals) <- runTactic tac $ J.empty ty
  case subgoals of
    [] -> do
      reportWarning $ render $ ppr ext
      return [ValD (VarP decName) (NormalB $ ext) []]
    _ -> hoistError $ UnsolvedGoals subgoals
