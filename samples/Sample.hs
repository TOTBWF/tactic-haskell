{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Sample where

import Control.Applicative

import Language.Haskell.TH
import Language.Haskell.Tactic

tactic "pair" [t| forall a b. a -> b -> (a,b) |] $ do
  forall
  intros_
  split
  assumption

tactic "foo" [t| forall a b c d. a -> (a -> b) -> (b -> c) -> (a, d -> c)|] $ do
  auto 5

tactic "&" [t| forall a b. a -> (a -> b) -> b |] $ do
  forall
  intros ["x", "f"]
  apply "f"
  exact "x"
