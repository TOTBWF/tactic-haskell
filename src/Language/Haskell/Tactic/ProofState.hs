{-# LANGUAGE DeriveTraversable #-}
module Language.Haskell.Tactic.ProofState
  ( ProofState(..)
  , axiom
  ) where

import Language.Haskell.TH

import Control.Monad(ap)

data ProofState jdg = ProofState [jdg] ([Exp] -> Exp)
  deriving (Functor, Foldable, Traversable)

axiom :: Exp -> ProofState jdg
axiom e = ProofState [] (const e)

instance Applicative ProofState where
  pure j = ProofState [j] head
  (<*>) = ap

instance Monad ProofState where
  return = pure
  (ProofState subgoals ext) >>= k =
    let build (ProofState s e) (sg, ext) =
          let n = length s
          in (s <> sg, \es -> (e $ take n es):(ext $ drop n es))
        (subgoals', ext') = foldr build ([], id) $ k <$> subgoals
    in ProofState subgoals' (ext . ext')
