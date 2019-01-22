{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Tactic.Internal.Judgement
  ( Judgement(..)
  , empty
  , extend
  , extends
  , remove
  , lookup
  ) where

import Prelude hiding (lookup)

import Data.Bifunctor

import Language.Haskell.TH
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib hiding (empty, (<>))

import Language.Haskell.Tactic.Internal.Telescope (Telescope(..), (@>))
import qualified Language.Haskell.Tactic.Internal.Telescope as Tl

-- | A @'Judgement'@ consists of a series of hypotheses (in this case, @'Name'@s bound to @'Type'@s), along with a goal (@'Type'@).
data Judgement = Judgement (Telescope String (Exp, Type)) Type
  deriving (Show)

instance Ppr Judgement where
  ppr (Judgement hyps goal) =
    let pprHyps = vcat $ fmap (\(x, (_, t)) -> text x <+> text "::" <+> ppr t) $ Tl.toList hyps
        delim = text "==============="
        pprGoal = ppr goal
    in pprHyps $$ delim $$ pprGoal

-- | Empty @'Judgement'@.
empty :: Type -> Judgement
empty t = Judgement (mempty) t

-- | Extend a @'Judgement'@ with a hypothesis.
extend :: String -> Exp -> Type -> Judgement -> Judgement
extend x e t (Judgement hyps goal) = Judgement (hyps @> (x,(e, t))) goal

-- | Extend a @'Judgement'@ with a telescope.
extends :: Telescope String (Exp, Type) -> Judgement -> Judgement
extends tl (Judgement hyps goal) = Judgement (hyps <> tl) goal

-- | Remove a hypothesis from a @'Judgement'@
remove :: String -> Judgement -> Judgement
remove n (Judgement hyps goal) = Judgement (Tl.remove n hyps) goal

-- | Look up a hypothesis variable in a @'Judgement'@. Note that this uses @'nameBase'@ for comparison.
lookup :: String -> Judgement -> Maybe (Exp, Type)
lookup x (Judgement hyps _) = fmap snd $ Tl.findVar ((== x)) hyps
