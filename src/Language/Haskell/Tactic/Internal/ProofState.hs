
-- |
-- Module      :  Language.Haskell.Tactic.Internal.ProofState
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = The Proof State
--
-- This module provides the standard LCF definition of a proof state.
-- However, there are a couple of interesting points. Namely, @'ProofState' jdg@
-- is parameterized, which means that @'ProofState'@ becomes a @'Monad'@!
{-# LANGUAGE DeriveTraversable #-}
module Language.Haskell.Tactic.Internal.ProofState
  ( ProofState(..)
  , axiom
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib hiding (empty, (<>))
import qualified Language.Haskell.TH.PprLib as P

import Control.Monad(ap)

-- | A @'ProofState'@ is a list of subgoals of type @jdg@, along
-- with a function that takes the extract of each of the subgoals,
-- and creates a new extract.
data ProofState jdg = ProofState [jdg] ([Exp] -> Exp)
  deriving (Functor, Foldable, Traversable)

instance (Ppr jdg) => Ppr (ProofState jdg) where
  ppr (ProofState subgoals _) =
    vcat $ fmap (\(i,sg) -> int i P.<> text ")" <+> ppr sg) $ zip [1 ..] subgoals

-- | Creates a proof state with no subgoals.
axiom :: Exp -> ProofState jdg
axiom e = ProofState [] (const e)

instance Applicative ProofState where
  pure j = ProofState [j] head
  (<*>) = ap

instance Monad ProofState where
  return = pure
  (ProofState subgoals ext) >>= k =
    let build (ProofState s e) (sg, ext) =
          let n = length s
          in (s <> sg, \es -> (e $ take n es):(ext $ drop n es))
        (subgoals', ext') = foldr build ([], id) $ k <$> subgoals
    in ProofState subgoals' (ext . ext')
