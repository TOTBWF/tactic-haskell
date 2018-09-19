{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -ddump-splices #-}

import Language.Haskell.Tactic
import Language.Haskell.Tactic.RebindableSyntax

import Prelude (IO, return, ($))

main :: IO ()
main = return ()


f = $(tactic [t| forall a b. a -> b -> (a,b)|] $ do
  intro
  x <- intro
  y <- intro
  intro <..> [use x, use y]
  )
  -- intro <..> [use x, use y])

