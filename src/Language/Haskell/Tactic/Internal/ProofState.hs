
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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Haskell.Tactic.Internal.ProofState
  ( ProofStateT(..)
  , axiom
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

newtype ProofStateT m jdg = ProofStateT { unProofStateT :: Client jdg Exp m Exp }

instance (Monad m) => Functor (ProofStateT m) where
  fmap f (ProofStateT p) = ProofStateT $ (request . f) >\\ p

instance (MonadError err m) => Alt (ProofStateT m) where
  (ProofStateT p1) <!> (ProofStateT p2) = ProofStateT $ p1 `catchError` (const p2)

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

instance (MonadError err m) => MonadError err (ProofStateT m) where
  throwError err = ProofStateT $ throwError err
  catchError (ProofStateT m) handler = ProofStateT $ catchError m (unProofStateT . handler)

-- Create a @'ProofState'@ with no subgoals.
axiom :: (Monad m) => Exp -> ProofStateT m jdg
axiom e = ProofStateT $ return e

-- subgoal :: (Monad m) => jdg -> ProofStateT m Exp
-- subgoal j = ProofStateT $ do
--   e <- request j
--   _h $ e
