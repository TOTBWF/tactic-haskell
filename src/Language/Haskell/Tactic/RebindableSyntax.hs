{-# LANGUAGE NoImplicitPrelude #-}
module Language.Haskell.Tactic.RebindableSyntax where

import Prelude ((<>))

import Language.Haskell.Tactic

(>>) :: Tactic -> Tactic -> Tactic
(>>) = (<>)

(>>=) :: Tactic -> (Name -> Tactic) -> Tactic
t >>= f = t <> with f
