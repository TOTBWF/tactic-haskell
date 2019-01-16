{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -ddump-splices #-}

import Language.Haskell.TH
import Language.Haskell.Tactic

main :: IO ()
main = return ()


-- p :: forall a b. a -> b -> (a, b)
-- p = $(solveWith [t| a -> b -> (a,b)|] $ do
--   x <- lam
--   y <- lam
--   tuple <..> [use x, use y])
  -- tuple <..> [use x, use y])
  -- each [])
  -- intro <..> [use x, use y])

-- foo :: a
-- foo = $(reify 'foo *> fail "Oh no")

-- f :: forall a b. a -> (a -> b) -> b
-- f = $(solveWith [t| a -> (a -> b) -> b |] $ do
--   x <- lam
--   f <- lam
--   v <- elim f)
-- f = $(tactic [t| forall a b. a -> (a -> b) -> b|] $ do
--   intro
--   x <- intro
--   f <- intro
--   elim f
--   assumption)

-- foo :: forall a. [a] -> Maybe a
-- foo = $(tactic [t| [a] -> Maybe a |] $ do
--   xs <- intro
--   induction xs <..>
--     [ use [| Nothing :: Maybe a |]
--     , with $ \x -> use [| Just $(useName x) :: Maybe a |]
--     ]
--   )
