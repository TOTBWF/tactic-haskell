{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -ddump-splices #-}

import Language.Haskell.Tactic
import Language.Haskell.Tactic.RebindableSyntax

import Prelude hiding ((>>), (>>=))

main :: IO ()
main = return ()


p = $(tactic [t| forall a b. a -> b -> (a,b)|] $ do
  intro
  x <- intro
  y <- intro
  intro <..> [use x, use y])

f = $(tactic [t| forall a b. a -> (a -> b) -> b|] $ do
  intro
  x <- intro
  f <- intro
  elim f
  assumption)

foo :: forall a. [a] -> Maybe a
foo = $(tactic [t| [a] -> Maybe a |] $ do
  xs <- intro
  induction xs <..>
    [ use [| Nothing :: Maybe a |]
    , with $ \x -> use [| Just $(useName x) :: Maybe a |]
    ]
  )
