{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Tactic.Judgement
  ( Judgement(..)
  , Expr
  , empty
  , extend
  , extends
  , remove
  , lookup
  , substJdg
  -- * Re-Exports
  , Type
  ) where

import Prelude hiding (lookup)

import Data.Bifunctor

-- import Data.Text.Prettyprint.Doc
import Outputable (Outputable(..), (<+>))
import qualified Outputable as P

import HsExpr
import HsExtension
import TyCoRep

import Language.Haskell.Tactic.Patterns
import Language.Haskell.Tactic.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Telescope as Tl


-- | A @'Judgement'@ consists of a series of hypotheses (in this case, @'Name'@s bound to @'Type'@s), along with a goal (@'Type'@).
data Judgement = Judgement (Telescope String (Expr, Type)) Type

instance Outputable Judgement where
  ppr (Judgement hyps goal) =
    let pprHyps = P.vcat $ fmap (\(x, (_, t)) -> P.text x <+> P.text "::" <+> pprType t) $ Tl.toList hyps
        delim = P.text "=============="
        pprGoal = pprType goal
    in P.vcat [pprHyps, delim, pprGoal]

-- | Empty @'Judgement'@.
empty :: Type -> Judgement
empty t = Judgement (mempty) t

-- | Extend a @'Judgement'@ with a hypothesis.
extend :: String -> Expr -> Type -> Judgement -> Judgement
extend x e t (Judgement hyps goal) = Judgement (hyps @> (x,(e, t))) goal

-- | Extend a @'Judgement'@ with a telescope.
extends :: Telescope String (Expr, Type) -> Judgement -> Judgement
extends tl (Judgement hyps goal) = Judgement (hyps <> tl) goal

-- | Remove a hypothesis from a @'Judgement'@
remove :: String -> Judgement -> Judgement
remove n (Judgement hyps goal) = Judgement (Tl.remove n hyps) goal

-- | Look up a hypothesis variable in a @'Judgement'@. Note that this uses @'nameBase'@ for comparison.
lookup :: String -> Judgement -> Maybe (Expr, Type)
lookup x (Judgement hyps _) = fmap snd $ Tl.findVar ((== x)) hyps

-- | Apply a @'TCvSubst'@ to a @'Judgment'@.
substJdg :: TCvSubst -> Judgement -> Judgement
substJdg subst (Judgement hy goal) = Judgement (fmap (second (substTy subst)) hy) (substTy subst goal)