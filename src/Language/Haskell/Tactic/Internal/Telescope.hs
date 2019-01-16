{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Language.Haskell.Tactic.Internal.Telescope
  (
    Telescope(..)
  , empty
  , singleton
  , extend
  , (@>)
  , foldlWithVar, foldrWithVar
  , foldlMWithVar, foldrMWithVar
  , toList
  , filter
  , lookup
  , find
  , findVar
  , remove
  ) where

import Prelude hiding (filter, lookup)

import Data.Bifunctor

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr
import qualified Language.Haskell.TH.PprLib as P

data Telescope v t
  = Empty
  | Snoc (Telescope v t) v t
  deriving (Show, Functor, Foldable, Traversable)

instance (Ppr v, Ppr t) => Ppr (Telescope v t) where
  ppr tl = commaSepWith (\(x,t) -> ppr x P.<> P.text "::" P.<> ppr t) (toList tl)

instance Semigroup (Telescope v t) where
  Empty <> t = t
  t <> Empty = t
  tl <> (Snoc tl' x a) = Snoc (tl <> tl') x a

instance Monoid (Telescope v t) where
  mempty = Empty

instance Bifunctor Telescope where
  first f Empty = Empty
  first f (Snoc tl v t) = Snoc (first f tl) (f v) t

  second f Empty = Empty
  second f (Snoc tl v t) = Snoc (second f tl) v (f t)

empty :: Telescope v t
empty = Empty

singleton :: v -> t -> Telescope v t
singleton x t = Snoc Empty x t

extend :: v -> t -> Telescope v t -> Telescope v t
extend x t tl = Snoc tl x t

(@>) :: Telescope v t -> (v, t) -> Telescope v t
tl @> (v, t) = Snoc tl v t

foldlWithVar :: (b -> v -> a -> b) -> b -> Telescope v a -> b
foldlWithVar _ b Empty         = b
foldlWithVar f b (Snoc tl x a) = f (foldlWithVar f b tl) x a

foldrWithVar :: (v -> a -> b -> b) -> b -> Telescope v a -> b
foldrWithVar _ b Empty         = b
foldrWithVar f b (Snoc tl x a) = foldrWithVar f (f x a b) tl

foldlMWithVar :: (Monad m) => (b -> v -> a -> m b) -> b -> Telescope v a -> m b
foldlMWithVar _ b Empty = return b
foldlMWithVar f b (Snoc tl x a) = do
  b' <- foldlMWithVar f b tl
  f b' x a

foldrMWithVar :: (Monad m) => (v -> a -> b -> m b) -> b -> Telescope v a -> m b
foldrMWithVar _ b Empty = return b
foldrMWithVar f b (Snoc tl x a) = do
  b' <- f x a b
  foldrMWithVar f b' tl

filter :: (t -> Bool) -> Telescope v t -> Telescope v t
filter _ Empty = Empty
filter f (Snoc tl x a) | f a = Snoc (filter f tl) x a
                       | otherwise = filter f tl

toList :: Telescope v t -> [(v,t)]
toList = foldrWithVar (\x t -> (:) (x,t)) []

lookup :: (Eq v) => v -> Telescope v t -> Maybe t
lookup _ Empty = Nothing
lookup x (Snoc tl y t) | x == y = Just t
                       | otherwise = lookup x tl

find :: (t -> Bool) -> Telescope v t -> Maybe (v, t)
find f Empty = Nothing
find f (Snoc tl x t) | f t = Just (x, t)
                     | otherwise = find f tl

findVar :: (v -> Bool) -> Telescope v t -> Maybe (v, t)
findVar f Empty = Nothing
findVar f (Snoc tl x t) | f x = Just (x, t)
                        | otherwise = findVar f tl

remove :: (Eq v) => v -> Telescope v t -> Telescope v t
remove _ Empty = Empty
remove x (Snoc tl y t) | x == y = tl
                       | otherwise = Snoc (remove x tl) y t
