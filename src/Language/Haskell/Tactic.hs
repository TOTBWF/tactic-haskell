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
module Language.Haskell.Tactic
  ( Tactic
  , Name
  , MultiTactic
  , identity
  , compose
  , (<..>)
  , orElse
  , (<||>)
  , try
  , many
  , (?)
  , with
  , use
  , trustme
  , assumption
  , intro
  , elim
  , induction
  , tactic
  ) where

import Control.Monad.Writer.Strict
import Control.Monad.IO.Class
import Control.Monad.Fail (MonadFail)

import Data.Foldable hiding (all)

import Data.String (IsString(..))

import Data.Traversable.Extensions
import Data.Typeable

import Prelude hiding (all, or)

import qualified Text.PrettyPrint as P (render)

import Language.Haskell.TH
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib (Doc)
import qualified Language.Haskell.TH.PprLib as P
import Language.Haskell.TH.Syntax hiding (lift)

import Language.Haskell.Tactic.MetaSubst
import Language.Haskell.Tactic.Telescope (Telescope(..))
import qualified Language.Haskell.Tactic.Telescope as Tl
import Language.Haskell.Tactic.ProofState
import Language.Haskell.Tactic.Judgement
import Language.Haskell.Tactic.TH

newtype Tac j = Tac { unTac :: j -> Q (ProofState j) }

type Tactic = Tac Judgement
type MultiTactic = Tac (ProofState Judgement)

{- Tactic Combinators -}

-- | Identity Tactic. Does absolutely nothing.
identity :: Tactic
identity = Tac $ goal

compose :: Tactic -> MultiTactic -> Tactic
compose (Tac t) (Tac mt) = Tac $ fmap flatten . mt <=< t

all :: Tactic -> MultiTactic
all (Tac t) = Tac $ traverse (t)

each :: [Tactic] -> MultiTactic
each ts = Tac $ fmap snd . mapAccumLM applyTac ts
  where
    applyTac (Tac t:ts) j = (ts,) <$> t j
    applyTac [] j            = ([],) <$> (unTac identity) j

instance Semigroup Tactic where
  t1 <> t2 = t1 `compose` (all t2)

instance Monoid Tactic where
  mempty = identity

-- | Run the 1st tactic, and then run each of the tactics in the list on a resulting subgoal.
(<..>) :: Tactic -> [Tactic] -> Tactic
t <..> ts = t `compose` (each ts)

-- | Runs the 1st tactic, and if it fails, runs the 2nd>
orElse :: Tactic -> Tactic -> Tactic
orElse (Tac t1) (Tac t2) = Tac $ \j -> recover (t2 j) (t1 j)

-- | Combinator version of `orElse`
(<||>) :: Tactic -> Tactic -> Tactic
t1 <||> t2 = t1 `orElse` t2

-- | Tries to run the given tactic, and does nothing if it fails.
try :: Tactic -> Tactic
try t = t <||> identity

-- | Runs a tactic repeatedly.
many :: Tactic -> Tactic
many t = try (t <> many t)

render :: Doc -> String
render = P.render . P.to_HPJ_Doc

-- | Traces out the proof state at a given point with the provided label
(?) :: String -> Tactic
(?) t = Tac $ \j -> do
  reportWarning $ render $ "?" P.<> P.text t P.<> ":" P.<+> ppr j
  (unTac identity) j

instance IsString Doc where
  fromString = P.text

data Error
  = NoVariables
  | UndefinedVariable Name
  | AssumptionError Type
  | TypeMismatch { expectedType :: Type, expr :: Exp, exprType :: Type }
  | GoalMismatch { tacName :: String, appliedGoal :: Type }
  | UnsolvedGoals [Judgement]
  | NotImplemented String

tacticError :: Error -> Judgement -> Q a
tacticError e j =
  let errText = case e of
        NoVariables -> "No variables to bring into scope"
        UndefinedVariable x -> "Undefined variable" P.<+> ppr x
        AssumptionError t -> "Couldn't find any variables of type" P.<+> ppr t
        TypeMismatch{..} ->
          "Expected Type" P.<+> ppr expectedType P.<+> "but" P.<+> ppr expr P.<+> "has type" P.<+> ppr exprType P.$+$
            "Expected Type (Debug):" P.<+> (P.text $ show expectedType) P.$+$
            "Actual Type (Debug):" P.<+> (P.text $ show exprType)
        GoalMismatch{..} ->
          "Tactic" P.<+> P.text tacName P.<+> "doesn't support goals of the form" P.<+> ppr appliedGoal P.$+$
            "Debug:" P.<+> (P.text $ show appliedGoal)
        NotImplemented t -> P.text t P.<+> "isn't implemented yet"
  in fail $ render $ "Tactic Error:" P.<+> errText P.$+$ "Proof State:" P.<+> ppr j

lookupHyp' :: Name -> Judgement -> TacticT Type
lookupHyp' x j =
  case lookupHyp x j of
    Just t -> return t
    Nothing -> lift $ tacticError (UndefinedVariable x) j

-- TODO: Remove variables from hypotheses after with block
-- TODO: Use TH to inspect the name that the name is being given
-- | Brings a name from the context into scope
with :: (Name -> Tactic) -> Tactic
with f = Tac $ \j ->
  case popHidden j of
    Just (x, j') -> (unTac $ f x) j'
    Nothing -> tacticError NoVariables j

-- | Uses a piece of evidence to try to prove the goal
use :: Name -> Tactic
use x = mkTactic $ \j ->
  let checkType t =
        if t == (goalType j)
        then return (VarE x)
        else lift $ tacticError (TypeMismatch (goalType j) (VarE x) t) j
  in case lookupHyp x j of
    Just t -> checkType t
    Nothing -> (lift $ reify x) >>= \case
      VarI _ t _ -> checkType t
      DataConI _ t _ -> checkType t
      d -> lift $ tacticError (NotImplemented $ show d) j

{- Tactic Helpers-}
type TacticT = WriterT (Telescope Judgement) Q

subgoal ::  Judgement -> TacticT Name
subgoal j = do
  x <- lift $ metavar
  tell (Tl.singleton x j)
  return x

mkTactic :: (Judgement -> TacticT Exp) -> Tactic
mkTactic f = Tac $ \j -> do
  (e, goals) <- runWriterT (f j)
  return $ ProofState goals e

-- | Searches the hypotheses for any type that may match the goal
assumption :: Tactic
assumption = mkTactic $ \j@Judgement{..} ->
  case find ((== goalType) . snd) (Tl.toList $ hypotheses <> hidden) of
    Just (x, _) -> return $ VarE x
    Nothing -> lift $ tacticError (AssumptionError goalType) j

{-# WARNING trustme "Completely unsafe, will generate code that will crash" #-}
trustme :: Tactic
trustme = mkTactic $ \_ -> lift [| error "trustme called" |]

-- | Introduces new hypotheses. Operates on functions and pairs.
intro :: Tactic
intro = mkTactic $ \j@Judgement{..} -> case goalType of
  Function a b -> do
    x <- lift $ newName "x"
    mx <- subgoal $ withGoal b $ extendHyp x a j
    return $ LamE [VarP x] (UnboundVarE mx)
  ForallT _ _ t -> do
    mx <- subgoal $ withGoal t j
    return $ UnboundVarE mx
  Tuple ts -> do
    mxs <- traverse (\t -> fmap UnboundVarE $ subgoal $ withGoal t j) ts
    return $ TupE mxs
  t -> lift $ tacticError (GoalMismatch "intro" t) j

-- | Does function application
elim :: Name -> Tactic
elim f = mkTactic $ \j@Judgement{..} -> lookupHyp' f j >>= \case
  Function a b -> do
    -- Prove that if we actually applied the function, we could solve the goal
    fx <- lift $ newName "fx"
    mfx <- subgoal $ extendHyp fx b j
    -- Prove that we can actually apply the function
    mx <- subgoal $ withGoal a $ removeHyp f j
    -- This is kind of a hack. We can't substitute all occurances of 'fx' in 'mfx' for 'mx' 
    -- so transform it into 'let fx = mx in mfx', which accomplishes the same thing
    return $ LetE [ValD (VarP fx) (NormalB $ AppE (VarE f) (UnboundVarE mx)) []] (UnboundVarE mfx)
  t -> lift $ tacticError (GoalMismatch "elim" t) j

induction :: Name -> Tactic
induction n = mkTactic $ \j@Judgement{..} -> lookupHyp' n j >>= \case
  -- Constructor x _ ->
  --   (lift $ reify x) >>= \case
  --   TyConI (DataD _ _ tvs _ ctrs _) -> do
  --     -- For each of the constructors, create an inductive goal
  --     cs <- for ctrs $ \case
  --       (NormalC n (fmap snd -> ts)) -> do
  --         -- Bring all of the types from the constructor into the hypotheses
  --         (j', ps) <- lift $ foldlM (\(jd, ns) ty -> do
  --                          x <- newName "_"
  --                          return $ (extendHyp x ty jd, (VarP x):ns)
  --                         ) (j, []) ts
  --         mx <- subgoal j'
  --         -- Prove the original goal using the assumed stuff
  --         return $ Match (ConP n (reverse ps)) (NormalB $ UnboundVarE mx) []
  --       c -> lift $ tacticError (NotImplemented $ "Induction on fancy constructor:" ++ show c) j
  --     return $ CaseE (VarE x) cs
    -- i -> lift $ tacticError (NotImplemented $ "Induction on fancy data:" ++ show i) j
  List t -> do
    -- Create a subgoal of the empty case
    emx <- subgoal j
    -- Create a subgoal for the cons case
    x <- lift $ newName "x"
    xs <- lift $ newName "xs"
    cmx <- subgoal $ extendHyp x t $ extendHyp xs (List t) j
    -- Build a match clause
    let consMatch = Match (InfixP (VarP x) '(:) (VarP xs)) (NormalB $ UnboundVarE cmx) []
    let emptyMatch = Match (ConP '[] []) (NormalB $ UnboundVarE emx) []
    return $ CaseE (VarE n) [consMatch, emptyMatch]
  t -> lift $ tacticError (GoalMismatch "induction" t) j

-- | Runs a tactic against a given type
tactic :: Q Type -> Tactic -> Q Exp
tactic goal t = do
  g <- goal
  (ProofState goals ext) <- unTac t $ emptyHyp g
  case goals of
    Empty -> return ext
    js -> fail $ render $ "Unsolved Goals:" P.$+$  P.vcat (fmap (ppr . snd) $ Tl.toList js)

-- -- | Runs a tactic against a given type, and creates a s
-- define :: Q Type -> Tactic -> Q [Dec]
-- define goal t = do
--   g <- goal
--   (ProofState goals ext) <- unTac t $ emptyHyp g
--   case goals of
--     Empty -> return ext
--     js -> fail $ render $ "Unsolved Goals:" P.$+$  P.vcat (fmap (ppr . snd) $ Tl.toList js)
