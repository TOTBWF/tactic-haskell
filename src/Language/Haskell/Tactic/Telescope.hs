{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Haskell.Tactic.Telescope
  (
    Telescope(..)
  , empty
  , singleton
  , (@>)
  , foldlWithVar, foldrWithVar
  , foldlMWithVar, foldrMWithVar
  , toList
  , filter
  , lookup
  , remove
  ) where

import Prelude hiding (filter, lookup)

import GHC.Generics (Generic)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr
import qualified Language.Haskell.TH.PprLib as P

import Language.Haskell.Tactic.MetaSubst

data Telescope t
  = Empty
  | Snoc (Telescope t) Name t
  deriving (Show, Functor, Foldable, Traversable, Generic)

instance (MetaSubst t) => MetaSubst (Telescope t)

instance (Ppr t) => Ppr (Telescope t) where
  ppr tl = commaSepWith (\(x,t) -> ppr x P.<> P.char ':' P.<> ppr t) (toList tl)

instance Semigroup (Telescope t) where
  Empty <> t = t
  t <> Empty = t
  tl <> (Snoc tl' x a) = Snoc (tl <> tl') x a

instance Monoid (Telescope t) where
  mempty = Empty

empty :: Telescope t
empty = Empty

singleton :: Name -> t -> Telescope t
singleton x t = Snoc Empty x t

(@>) :: Telescope t -> (Name, t) -> Telescope t
tl @> (v, t) = Snoc tl v t

foldlWithVar :: (b -> Name -> a -> b) -> b -> Telescope a -> b
foldlWithVar _ b Empty         = b
foldlWithVar f b (Snoc tl x a) = f (foldlWithVar f b tl) x a

foldrWithVar :: (Name -> a -> b -> b) -> b -> Telescope a -> b
foldrWithVar _ b Empty         = b
foldrWithVar f b (Snoc tl x a) = foldrWithVar f (f x a b) tl

foldlMWithVar :: (Monad m) => (b -> Name -> a -> m b) -> b -> Telescope a -> m b
foldlMWithVar _ b Empty = return b
foldlMWithVar f b (Snoc tl x a) = do
  b' <- foldlMWithVar f b tl
  f b' x a

foldrMWithVar :: (Monad m) => (Name -> a -> b -> m b) -> b -> Telescope a -> m b
foldrMWithVar _ b Empty = return b
foldrMWithVar f b (Snoc tl x a) = do
  b' <- f x a b
  foldrMWithVar f b' tl

filter :: (t -> Bool) -> Telescope t -> Telescope t
filter _ Empty = Empty
filter f (Snoc tl x a) | f a = Snoc (filter f tl) x a
                       | otherwise = filter f tl

toList :: Telescope t -> [(Name,t)]
toList = foldrWithVar (\x t -> (:) (x,t)) []

lookup :: Name -> Telescope t -> Maybe t
lookup _ Empty = Nothing
lookup x (Snoc tl y t) | x == y = Just t
                       | otherwise = lookup x tl

remove :: Name -> Telescope t -> Telescope t
remove _ Empty = Empty
remove x (Snoc tl y t) | x == y = tl
                       | otherwise = Snoc (remove x tl) y t
