{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Annotation
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures. All definitions are
-- generalised versions of those in "Data.Comp.Annotation".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Annotation
    (
     (:&:) (..),
     DistAnn (..),
     RemA (..),
     liftA,
     ann,
     liftA',
     stripA,
     propAnn,
     project',

     AnnotateSummand,
     addAnn,
     remAnn,
     remAnnTerm
    ) where

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import qualified Data.Comp.Ops as O
import Data.Comp.SubsumeCommon
import Data.Kind

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
liftA :: (RemA s s') => (s' a :-> t) -> s a :-> t
liftA f v = f (remA v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

ann :: (DistAnn f p g, HFunctor f) => p -> CxtFun f g
ann c = appSigFun (injectA c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
liftA' :: (DistAnn s' p s, HFunctor s')
       => (s' a :-> Cxt h s' a) -> s a :-> Cxt h s a
liftA' f v = let (v' O.:&: p) = projectA v
             in ann p (f v')

{-| This function strips the annotations from a term over a
functor with annotations. -}

stripA :: (RemA g f, HFunctor g) => CxtFun g f
stripA = appSigFun remA


propAnn :: (DistAnn f p f', DistAnn g p g', HFunctor g)
               => Hom f g -> Hom f' g'
propAnn alg f' = ann p (alg f)
    where (f O.:&: p) = projectA f'

-- | This function is similar to 'project' but applies to signatures
-- with an annotation which is then ignored.
project' :: (RemA f f', s :<: f') => Cxt h f a i -> Maybe (s (Cxt h f a) i)
project' (Term x) = proj $ remA x
project' _ = Nothing

class AnnotateSummand' (e :: Emb)
                      (t :: (Type -> Type) -> Type -> Type)
                      (v :: Type)
                      (f :: (Type -> Type) -> Type -> Type)
                      (g :: (Type -> Type) -> Type -> Type) where
    addAnn' :: Proxy e -> Proxy t -> v -> SigFun f g
    remAnn' :: Proxy e -> Proxy t -> Proxy v -> SigFun g f

instance AnnotateSummand' (Found Here) f v f (f :&: v) where
    addAnn' _ _ = flip (:&:)
    remAnn' _ _ _ (t :&: _) = t

instance AnnotateSummand' (Found p) t v f g => AnnotateSummand' (Found (Le p)) t v (f :+: g') (g :+: g') where
    addAnn' _ _ v (Inl x) = Inl $ addAnn' (P @(Found p)) (P @t) v x
    addAnn' _ _ _ (Inr x) = Inr x
    remAnn' _ _ _ (Inl x) = Inl $ remAnn' (P @(Found p)) (P @t) (P @v) x
    remAnn' _ _ _ (Inr x) = Inr x

instance AnnotateSummand' (Found p) t v f g => AnnotateSummand' (Found (Ri p)) t v (g' :+: f) (g' :+: g) where
    addAnn' _ _ v (Inr x) = Inr $ addAnn' (P @(Found p)) (P @t) v x
    addAnn' _ _ _ (Inl x) = Inl x
    remAnn' _ _ _ (Inr x) = Inr $ remAnn' (P @(Found p)) (P @t) (P @v) x
    remAnn' _ _ _ (Inl x) = Inl x

instance (AnnotateSummand' (Found p) t v f g, AnnotateSummand' (Found q) t v f' g') => AnnotateSummand' (Found (Sum p q)) t v (f :+: f') (g :+: g') where
    addAnn' _ _ v (Inl x) = Inl $ addAnn' (P @(Found p)) (P @t) v x
    addAnn' _ _ v (Inr x) = Inr $ addAnn' (P @(Found q)) (P @t) v x
    remAnn' _ _ _ (Inl x) = Inl $ remAnn' (P @(Found p)) (P @t) (P @v) x
    remAnn' _ _ _ (Inr x) = Inr $ remAnn' (P @(Found q)) (P @t) (P @v) x

type AnnotateSummand t v f g = (ComprEmb (Elem t f) ~ ComprEmb (Elem (t:&:v) g), AnnotateSummand' (ComprEmb (Elem t f)) t v f g)

addAnn :: forall t v f g . AnnotateSummand t v f g => v -> SigFun f g
addAnn = addAnn' (P @(ComprEmb (Elem t f))) (P @t)

remAnn :: forall t v f g . AnnotateSummand t v f g => SigFun g f
remAnn = remAnn' (P @(ComprEmb (Elem t f))) (P @t) (P @v)

remAnnTerm :: forall t v f g . (HFunctor g, AnnotateSummand t v f g) => CxtFun g f
remAnnTerm (Term t) = Term . remAnn @t @v $ hfmap (remAnnTerm @t @v) t
remAnnTerm (Hole x) = Hole x
