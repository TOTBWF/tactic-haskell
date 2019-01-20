-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Tactic.Internal.T
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Haskell.Tactic.Internal.T
  ( T(..)
  ) where

import Control.Applicative
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- | This monad exists soley to provide an @'Alternative'
-- instance to the @'Q' Monad.
newtype T a = T { runT :: Q a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, Quasi)

instance Alternative T where
  empty = fail "empty"
  (T t1) <|> (T t2) = T $ recover t2 t1
