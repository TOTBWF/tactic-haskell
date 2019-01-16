{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Sample where

import Control.Applicative

import Language.Haskell.Tactic

tactic "pair" [t| forall a b. a -> b -> (a,b) |] $ do
  forall
  intros ["x", "y"]
  split ? "f"
  assumption

tactic "&" [t| forall a b. a -> (a -> b) -> b |] $ do
  forall
  intros ["x", "f"]
  apply "f"
  exact "x"
