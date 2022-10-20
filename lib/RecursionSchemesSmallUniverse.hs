{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE DataKinds, StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
module RecursionSchemesSmallUniverse where

import Prelude hiding (Functor)
import qualified Prelude

import Data.Kind
import Data.Proxy
import Debug.Trace
import Language.Haskell.Liquid.ProofCombinators
import Data.Typeable (typeRep)
import Type.Reflection

-- LiquidHaskell rejects @Fix@, which is an essential part of recursion
-- schemes.
-- 
-- @@
-- newtype Fix f = Fix (f (Fix f))
-- @@
-- 
-- @@
-- lib/SmallUniverseFunctor.hs:38:1-31: error:
--     • Negative occurence of SmallUniverseFunctor.Fix in SmallUniverseFunctor.Fix : forall (f :: * -> *).
-- @@
-- 
-- So we follow the "Universes for generic programming" section from page 30 of
-- <http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf>

type Functor :: Type
data Functor where
    Id   :: Functor
    K    :: Type -> Functor
    (:+) :: Functor -> Functor -> Functor
    (:*) :: Functor -> Functor -> Functor

type family Decode (_functor :: Functor) (_x :: Type) :: Type where
    Decode 'Id       x = x
    Decode ('K a)    x = a
    Decode (f ':+ g) x = Either (Decode f x) (Decode g x)
    Decode (f ':* g) x = (Decode f x, Decode g x)

type Mu :: Functor -> Type
newtype Mu f = MuIn { muOut :: Decode f (Mu f) }

-- We want to implement this map:
-- 
-- @@
-- map :: Proxy (f :: Functor) -> (a -> b) -> Decode f a -> Decode f b
-- @@
-- 
-- The normal way to branch on a type (the constructors of @Functor@) in
-- haskell is with a typeclass, so we could implement it with four
-- @Prelude.Functor@ instances:
-- 
-- @@
-- instance Prelude.Functor (Decode (f :: Functor)) where fmap :: (a -> b) -> Decode f a -> Decode f b
-- @@
--
-- @@
-- instance Prelude.Functor (Decode 'Id      ) where fmap :: (a -> b) -> Decode 'Id a -> Decode 'Id b
--                                                   fmap :: (a -> b) -> a -> b
-- instance Prelude.Functor (Decode ('K t)   ) where fmap :: (a -> b) -> Decode ('K t) a -> Decode ('K t) b
--                                                   fmap :: (a -> b) -> t -> t
-- instance Prelude.Functor (Decode (f ':+ g)) where fmap :: (a -> b) -> Decode (f ':+ g) a -> Decode (f ':+ g) b
--                                                   fmap :: (a -> b) -> Either (Decode f a) (Decode g a) -> Either (Decode f b) (Decode g b)
-- instance Prelude.Functor (Decode (f ':* g)) where fmap :: (a -> b) -> Decode (f ':* g) a -> Decode (f ':* g) b
--                                                   fmap :: (a -> b) -> (Decode f a, Decode g a) -> (Decode f a, Decode g a)
-- @@
-- 
-- But this @Prelude.Functor@ instance calls @Decode@ with too few type
-- arguments and so we can't even write it down. More information than you want
-- about that, over here:
-- <https://ryanglscott.github.io/2019/05/26/on-the-arity-of-type-families/>
--
-- An alternative might be to defunctionalize the call to @Decode@:
-- <https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/>
-- <https://blog.poisson.chat/posts/2018-08-06-one-type-family.html>
--
-- Before that, we could also try to use typeable.
