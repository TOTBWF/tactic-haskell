{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Sample where

import Control.Applicative

import Language.Haskell.TH
import Language.Haskell.Tactic

data Nat = Z | S Nat
  deriving (Show)

data List a = Nil | Cons a (List a)

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

tactic "if_" [t| forall a. a -> a -> Bool -> a |] $ do
  forall
  intros ["f", "t", "b"]
  induction "b" <@> [exact "f", exact "t"]

tactic "plus" [t| Nat -> Nat -> Nat |] $ do
  intros ["n", "m"]
  induction "n" <@>
    [ exact "m"
    , do
       apply 'S
       exact "ind"
    ]
