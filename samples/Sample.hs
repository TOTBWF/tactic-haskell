{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Sample where

import Language.Haskell.Tactic

tactic "pair" [t| forall a b. a -> b -> (a,b) |] $ do
  forall
  intro "x"
  intro "y"
  split <..> [exact "x", exact "y"]

tactic "&" [t| forall a b. a -> (a -> b) -> b |] $ do
  forall
  intro "x"
  intro "f"
  apply "f"
  exact "x"
