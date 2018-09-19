{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
module Language.Haskell.Tactic.Judgement
  ( Judgement(..)
  , emptyHyp
  , extendHyp
  , withGoal
  , lookupHyp
  , removeHyp
  , popHidden
  ) where

import GHC.Generics (Generic)

import Language.Haskell.TH
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib

import Language.Haskell.Tactic.MetaSubst
import Language.Haskell.Tactic.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Telescope as Tl

data Judgement = Judgement
  { hypotheses :: Telescope Type
  , hidden :: Telescope Type
  , goalType :: Type
  } deriving (Show, Generic)

instance MetaSubst Judgement

instance Ppr Judgement where
  ppr Judgement{..} = ppr hypotheses <+> char '⊢' <+> ppr goalType

emptyHyp :: Type -> Judgement
emptyHyp t = Judgement { hypotheses = mempty, hidden = mempty, goalType = t }

extendHyp :: Name -> Type -> Judgement -> Judgement
extendHyp x t j@Judgement{..} = j{ hidden = hidden @> (x,t) }

withGoal :: Type -> Judgement -> Judgement
withGoal t j@Judgement{..} = j{ goalType = t }

lookupHyp :: Name -> Judgement -> Maybe Type
lookupHyp x j@Judgement{..} = Tl.lookup x hypotheses

removeHyp :: Name -> Judgement -> Judgement
removeHyp x j@Judgement{..} = j { hypotheses = Tl.remove x hypotheses }

popHidden :: Judgement -> Maybe (Name, Judgement)
popHidden j@Judgement{..} =
  case hidden of
    Snoc tl x t -> Just (x, j { hidden = tl, hypotheses = hypotheses @> (x,t) })
    Empty -> Nothing
