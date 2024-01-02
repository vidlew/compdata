{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}



--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Projection
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides a generic projection function 'pr' for
-- arbitrary nested binary products.
--
--------------------------------------------------------------------------------


module Data.Comp.Projection (pr, (:<), (:>), mapFactor) where

import Data.Comp.SubsumeCommon
import Data.Kind

type family Elem (f :: Type)
                 (g :: Type) :: Emb where
    Elem f f = Found Here
    Elem (f1, f2) g =  Sum' (Elem f1 g) (Elem f2 g)
    Elem f (g1, g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound

class Proj (e :: Emb) (p :: Type)
                      (q :: Type) where
    pr'  :: Proxy e -> q -> p

instance Proj (Found Here) f f where
    pr' _ = id

instance Proj (Found p) f g => Proj (Found (Le p)) f (g, g') where
    pr' _ = pr' (P :: Proxy (Found p)) . fst


instance Proj (Found p) f g => Proj (Found (Ri p)) f (g', g) where
    pr' _ = pr' (P :: Proxy (Found p)) . snd


instance (Proj (Found p1) f1 g, Proj (Found p2) f2 g)
    => Proj (Found (Sum p1 p2)) (f1, f2) g where
    pr' _ x = (pr' (P :: Proxy (Found p1)) x, pr' (P :: Proxy (Found p2)) x)


infixl 5 :<
--infixl 5 :~<
infixl 5 :>

type family IsFound (e :: Emb) :: Bool where
    IsFound NotFound = False
    IsFound (Found _) = True

-- | The constraint @e :< p@ expresses that @e@ is a component of the
-- type @p@. That is, @p@ is formed by binary products using the type
-- @e@. The occurrence of @e@ must be unique. For example we have @Int
-- :< (Bool,(Int,Bool))@ but not @Bool :< (Bool,(Int,Bool))@.

type f :< g = --(IsFound (ComprEmb (Elem f g)) ~ True,
              Proj (ComprEmb (Elem f g)) f g
              --, ModifyFactor (ComprEmb (Elem f g)) g f
              --)
--type f :~< g = IsFound (ComprEmb (Elem f g)) ~ False
type f :> g = g :< f


-- | This function projects the component of type @e@ out or the
-- compound value of type @p@.

pr :: forall p q . (p :< q) => q -> p
pr = pr' (P :: Proxy (ComprEmb (Elem p q)))

type family AddFactor' (e :: Emb) (v :: Type) (w :: Type) :: Type where
    AddFactor' (Found _) v w = v
    AddFactor' NotFound v w = (v,w)
    AddFactor' Ambiguous v w = v

type AddFactor v w = AddFactor' (ComprEmb (Elem w v)) v w

addFactor :: (ComprEmb (Elem w v) ~ NotFound) => w -> v -> AddFactor v w
addFactor w v = (v,w)

class ModifyFactor (e :: Emb) v w where
    modifyFactor' :: Proxy e -> v -> w -> w

instance ModifyFactor (Found Here) v v where
    modifyFactor' _ v _ = v

instance (ModifyFactor (Found e) u w, ModifyFactor (Found f) v w) => ModifyFactor (Found (Sum e f)) (u,v) w where
    modifyFactor' _ (u,v) w = modifyFactor' (P @(Found e)) u $ modifyFactor' (P @(Found f)) v w

instance (ModifyFactor (Found e) u w) => ModifyFactor (Found (Le e)) u (w,v) where
    modifyFactor' _ u (w,v) = (modifyFactor' (P @(Found e)) u w, v)

instance (ModifyFactor (Found e) u v) => ModifyFactor (Found (Ri e)) u (w,v) where
    modifyFactor' _ u (w,v) = (w, modifyFactor' (P @(Found e)) u v)

modifyFactor :: forall u v. (u :< v, ModifyFactor (ComprEmb (Elem u v)) u v) => u -> v -> v
modifyFactor = modifyFactor' $ P @(ComprEmb (Elem u v))


type family ReplaceFactor (e :: Emb) u v where
    ReplaceFactor (Found Here) u v = u
    ReplaceFactor (Found (Le e)) u (a,b) = (ReplaceFactor (Found e) u a,b)
    ReplaceFactor (Found (Ri e)) u (a,b) = (a,ReplaceFactor (Found e) u b)

class MapFactor (e :: Emb) s u where
    mapFactor' :: forall t . (s -> t) -> u -> (ReplaceFactor e t u)

instance MapFactor (Found Here) s s where
    mapFactor' f t = f t

instance (MapFactor (Found e) s u) => MapFactor (Found (Le e)) s (u,v) where
    mapFactor' f (u,v) = (mapFactor' @(Found e) f u, v)

instance (MapFactor (Found e) s v) => MapFactor (Found (Ri e)) s (u,v) where
    mapFactor' f (u,v) = (u, mapFactor' @(Found e) f v)

mapFactor :: forall s t u . (s :< u, MapFactor (ComprEmb (Elem s u)) s u) => (s -> t) -> u -> ReplaceFactor (ComprEmb (Elem s u)) t u
mapFactor = mapFactor' @(ComprEmb (Elem s u))
