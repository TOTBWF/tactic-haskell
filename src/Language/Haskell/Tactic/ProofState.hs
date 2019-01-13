{-# LANGUAGE DeriveTraversable #-}
module Language.Haskell.Tactic.ProofState
  ( ProofState(..)
  , axiom
  ) where

import Control.Monad(ap)

data ProofState ext jdg = ProofState [jdg] ([ext] -> ext)
  deriving (Functor, Foldable, Traversable)

axiom :: ext -> ProofState ext jdg
axiom e = ProofState [] (const e)

instance Applicative (ProofState ext) where
  pure j = ProofState [j] head
  (<*>) = ap

instance Monad (ProofState ext) where
  return = pure
  (ProofState subgoals ext) >>= k =
    let build (ProofState s e) (sg, ext) =
          let n = length s
          in (s <> sg, \es -> (e $ take n es):(ext $ drop n es))
        (subgoals', ext') = foldr build ([], id) $ k <$> subgoals
    in ProofState subgoals' (ext . ext')
