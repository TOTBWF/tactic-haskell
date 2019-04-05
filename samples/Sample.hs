{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Sample where


import Data.Function
import Language.Haskell.Tactic

data Nat = Z | S Nat
  deriving (Show)

data List a = Nil | Cons a (List a)
  deriving (Show)

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

-- No typeclass support yet for `apply`
add :: Int -> Int -> Int
add = (+)

tactic "sum'" [t| List Int -> Int |] $ do
  intro "x"
  induction "x" <@>
    [ exact (0 :: Integer)
    , do
        apply 'add <@> [exact "ind", exact "ind1"]
    ]

tactic "plus" [t| Nat -> Nat -> Nat |] $ do
  intros ["n", "m"]
  induction "n" <@>
    [ exact "m"
    , do
       apply 'S
       exact "ind"
    ]

tactic "trick" [t| forall a b c. Either a b -> (a -> c) -> (b -> c) -> c |] $
  auto 5

tactic "myFold" [t| forall a b. (a -> b -> b) -> b -> [a] -> b |] $ do
  auto 5

-- myFold' :: (a -> b -> b) -> b -> List a -> b
-- myFold' f b as = fix (\ffix x -> case x of Nil -> b; Cons ind ind1 -> f ind (ffix ind1)) as
