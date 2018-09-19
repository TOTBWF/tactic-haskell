{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Haskell.Tactic.ProofState
  (
    ProofState(..)
  , goal
  , flatten
  ) where

import GHC.Generics (Generic)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Language.Haskell.Tactic.MetaSubst
import qualified Language.Haskell.Tactic.Telescope as Tl
import Language.Haskell.Tactic.Telescope (Telescope)

data ProofState j = ProofState (Telescope j) Exp
  deriving (Functor, Foldable, Traversable, Generic)

instance (MetaSubst j) => MetaSubst (ProofState j)

goal :: (Quasi m) => j -> m (ProofState j)
goal j = do
  x <- metavar
  return $ ProofState (Tl.singleton x j) (UnboundVarE x)

flatten :: (MetaSubst j) => ProofState (ProofState j) -> ProofState j
flatten (ProofState goals ext) =
  let (goals', _, ext') = Tl.foldlWithVar build (mempty, [], ext) goals
  in (ProofState goals' ext')
  where
    build :: (MetaSubst j) => (Telescope j, [(Name, Exp)], Exp) -> Name -> ProofState j -> (Telescope j, [(Name, Exp)], Exp)
    build (tl, env, ext) x (ProofState tlx ax) =
      let tl' = tl <> metaSubsts env tlx
          env' = (x,ax):env
          ext' = metaSubst x ax ext
      in (tl', env', ext')

