{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Tactic.Judgement
  ( Judgement(..)
  , empty
  , extend
  , lookup
  ) where

import Prelude hiding (lookup)

import GHC.Generics (Generic)

import Language.Haskell.TH
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib hiding (empty)

import Language.Haskell.Tactic.MetaSubst
import Language.Haskell.Tactic.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Telescope as Tl

data Judgement = Judgement (Telescope Type) Type
  deriving (Show, Generic)

instance MetaSubst Judgement

instance Ppr Judgement where
  ppr (Judgement hyps goal) =
    let pprHyps = vcat $ fmap (\(x,t) -> ppr x <+> text "::" <+> ppr t) $ Tl.toList hyps
        delim = text "==============="
        pprGoal = ppr goal
    in pprHyps $$ delim $$ pprGoal

empty :: Type -> Judgement
empty t = Judgement (mempty) t

extend :: Name -> Type -> Judgement -> Judgement
extend x t (Judgement hyps goal) = Judgement (hyps @> (x,t)) goal

lookup :: Name -> Judgement -> Maybe Type
lookup x (Judgement hyps _) = Tl.lookup x hyps
-- emptyHyp :: Type -> Judgement
-- emptyHyp t = Judgement { hypotheses = mempty, hidden = mempty, goalType = t }

-- extendHyp :: Name -> Type -> Judgement -> Judgement
-- extendHyp x t j@Judgement{ hidden } = j{ hidden = hidden @> (x,t) }

-- withGoal :: Type -> Judgement -> Judgement
-- withGoal t j@Judgement{ goalType } = j{ goalType = t }

-- lookupHyp :: Name -> Judgement -> Maybe Type
-- lookupHyp x j@Judgement{ hypotheses } = Tl.lookup x hypotheses

-- removeHyp :: Name -> Judgement -> Judgement
-- removeHyp x j@Judgement{ hypotheses } = j { hypotheses = Tl.remove x hypotheses }

-- popHidden :: Judgement -> Maybe (Name, Judgement)
-- popHidden j@Judgement{ hypotheses, hidden } =
--   case hidden of
--     Snoc tl x t -> Just (x, j { hidden = tl, hypotheses = hypotheses @> (x,t) })
--     Empty -> Nothing
