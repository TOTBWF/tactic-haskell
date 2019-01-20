
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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
module Language.Haskell.Tactic.Internal.ProofState
  ( ProofStateT(..)
  , axiom
  , subgoal
  ) where

-- import Language.Haskell.TH.Ppr
-- import Language.Haskell.TH.PprLib hiding (empty, (<>))
-- import qualified Language.Haskell.TH.PprLib as P

import Data.Functor.Alt
import Control.Monad
import Control.Monad.Except
import Control.Monad.Fail as F
import Control.Monad.Trans
import Control.Monad.IO.Class

import Pipes.Core

import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.Tactic.Internal.T

newtype ProofStateT m jdg = ProofStateT { unProofStateT :: Client jdg Exp m Exp }

instance (Monad m) => Functor (ProofStateT m) where
  fmap f (ProofStateT p) = ProofStateT $ (request . f) >\\ p

-- instance () => Alt (ProofStateT m) where
--   (ProofStateT p1) <!> (ProofStateT p2) = ProofStateT $

instance (Monad m) => Applicative (ProofStateT m) where
  pure a = ProofStateT $ request a
  (ProofStateT pf) <*> (ProofStateT pa) = ProofStateT $ (\f -> (request . f) >\\ pa) >\\ pf

instance (Monad m) => Monad (ProofStateT m) where
  return = pure
  (ProofStateT p) >>= k = ProofStateT $ (unProofStateT . k) >\\ p

instance MonadTrans (ProofStateT ) where
  lift m = ProofStateT $ request =<< (lift m)

instance (MonadFail m) => MonadFail (ProofStateT m) where
  fail s = ProofStateT $ lift $ F.fail s

instance (MonadIO m) => MonadIO (ProofStateT m) where
  liftIO m = ProofStateT $ request =<< (liftIO m)

-- Create a @'ProofState'@ with no subgoals.
axiom :: (Monad m) => Exp -> ProofStateT m jdg
axiom e = ProofStateT $ return e

-- | Creates a @'ProofState'@ with a subgoal.
subgoal :: (Monad m) => jdg -> ProofStateT m jdg
subgoal j = ProofStateT $ request j
