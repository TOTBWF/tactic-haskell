{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Language.Haskell.Tactic.MetaSubst
  (
    MetaSubst (..)
  , metavar
  ) where

import Data.Foldable

import Data.Ratio
import Data.Word

import GHC.Generics hiding
  ( SourceUnpackedness
  , SourceStrictness
  , Fixity)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

metavar :: (Quasi m) => m Name
metavar = qNewName "?"

data SubstMeta e where
  SubstMeta :: (e ~ Exp) => Name -> SubstMeta e

-- | A typeclass for types that can participate in metavariable subsitution.
class MetaSubst e where

  isMetaVar :: e -> Maybe (SubstMeta e)
  isMetaVar _ = Nothing

  metaSubst :: Name -> Exp -> e -> e
  default metaSubst :: (Generic e, GMetaSubst (Rep e)) => Name -> Exp -> e -> e
  metaSubst n u x =
    case (isMetaVar x :: Maybe (SubstMeta e)) of
      Just (SubstMeta m) | n == m -> u
      _ -> to $ gmetaSubst n u (from x)

  metaSubsts :: [(Name, Exp)] -> e -> e
  default metaSubsts :: (Generic e, GMetaSubst (Rep e)) => [(Name, Exp)] -> e -> e
  metaSubsts ss x =
    case (isMetaVar x :: Maybe (SubstMeta e)) of
      Just (SubstMeta m) | Just (_,u) <- find ((== m)  . fst) ss -> u
      _ -> to $ gmetaSubsts ss (from x)

class GMetaSubst f where
  gmetaSubst :: Name -> Exp -> f a -> f a
  gmetaSubsts :: [(Name, Exp)] -> f a -> f a

instance (MetaSubst e) => GMetaSubst (K1 i e) where
  gmetaSubst nm val = K1 . metaSubst nm val . unK1
  gmetaSubsts ns = K1 . metaSubsts ns . unK1

instance (GMetaSubst f) => GMetaSubst (M1 i c f) where
  gmetaSubst nm val = M1 . gmetaSubst nm val . unM1
  gmetaSubsts ss = M1 . gmetaSubsts ss . unM1

instance GMetaSubst U1 where
  gmetaSubst _ _ _ = U1
  gmetaSubsts _ _ = U1

instance GMetaSubst V1 where
  gmetaSubst _ _ = id
  gmetaSubsts _ = id

instance (GMetaSubst f, GMetaSubst g) => GMetaSubst (f :*: g) where
  gmetaSubst nm val (f :*: g) = gmetaSubst nm val f :*: gmetaSubst nm val g
  gmetaSubsts ss (f :*: g) = gmetaSubsts ss f :*: gmetaSubsts ss g

instance (GMetaSubst f, GMetaSubst g) => GMetaSubst (f :+: g) where
  gmetaSubst nm val (L1 f) = L1 $ gmetaSubst nm val f
  gmetaSubst nm val (R1 g) = R1 $ gmetaSubst nm val g

  gmetaSubsts ss (L1 f) = L1 $ gmetaSubsts ss f
  gmetaSubsts ss (R1 g) = R1 $ gmetaSubsts ss g


instance MetaSubst Char where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst Integer where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst (Ratio b) where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst Word8 where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst Int  where
  metaSubst _ _ = id
  metaSubsts _ = id


instance (MetaSubst a, MetaSubst b) => MetaSubst (a,b)
instance (MetaSubst a, MetaSubst b, MetaSubst c) => MetaSubst (a,b,c)
instance (MetaSubst a) => MetaSubst (Maybe a)
instance (MetaSubst a) => MetaSubst [a]

instance MetaSubst Exp where
  isMetaVar (UnboundVarE x) = Just (SubstMeta x)
  isMetaVar _ = Nothing

instance MetaSubst Lit
instance MetaSubst Type
instance MetaSubst TyVarBndr
instance MetaSubst TyLit
instance MetaSubst Pat
instance MetaSubst Match
instance MetaSubst Body
instance MetaSubst Guard
instance MetaSubst Stmt
instance MetaSubst Dec
instance MetaSubst PatSynDir
instance MetaSubst PatSynArgs
instance MetaSubst Role
instance MetaSubst TypeFamilyHead
instance MetaSubst InjectivityAnn
instance MetaSubst FamilyResultSig
instance MetaSubst Pragma
instance MetaSubst AnnTarget
instance MetaSubst RuleBndr
instance MetaSubst Phases
instance MetaSubst TySynEqn
instance MetaSubst RuleMatch
instance MetaSubst Inline
instance MetaSubst Fixity
instance MetaSubst FixityDirection
instance MetaSubst Foreign
instance MetaSubst Safety
instance MetaSubst Callconv
instance MetaSubst Overlap
instance MetaSubst FunDep
instance MetaSubst DerivClause
instance MetaSubst DerivStrategy
instance MetaSubst Clause
instance MetaSubst Con
instance MetaSubst Bang
instance MetaSubst SourceUnpackedness
instance MetaSubst SourceStrictness
instance MetaSubst Range
 
instance MetaSubst Name where
  metaSubst _ _ = id
  metaSubsts _ = id
