{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-@ LIQUID "--reflection" @-}
module RelationsPLFA where

import Language.Haskell.Liquid.ProofCombinators ()

-- https://plfa.github.io/Relations/

data Nat = Zero | Suc Nat

zero    = Zero      {-@ reflect zero  @-}
one     = Suc zero  {-@ reflect one   @-}
two     = Suc one   {-@ reflect two   @-}
three   = Suc two   {-@ reflect three @-}
four    = Suc three {-@ reflect four  @-}

-- | Proposition that one nat is less than the other.
data LEProp = LE Nat Nat

-- Judgements-as-types encoding of the rules for less-than.
--
--  [z≤n] --------
--        zero ≤ n
--
--            m ≤ n
--  [s≤s] -------------
--        Suc m ≤ Suc n
--
data LERule where
    ZLEN :: Nat -> LERule
    SLES :: Nat -> Nat -> LERule -> LERule
------------------ {v:LERule | prop v = LE zero n}
{-@
data LERule where
    ZLEN :: n:_ -> Prop {LE zero n}
    SLES :: m:_ -> n:_ -> Prop {LE m n} -> Prop {LE (Suc m) (Suc n)}
@-}

{-@
ex1 :: Prop {LE zero three} @-}
ex1 = ZLEN three

{-@
ex2 :: Prop {LE two four} @-}
ex2 = SLES one three (SLES zero two (ZLEN two))

{-@
invSLES :: m:_ -> n:_ -> Prop {LE (Suc m) (Suc n)} -> Prop {LE m n} @-}
invSLES :: Nat -> Nat -> LERule -> LERule
invSLES _m _n (SLES __m __n mLEn) = mLEn




data EQProp a = EQ a a

data EQRule a where
    Refl :: a -> EQRule a
{-@
data EQRule a where
    Refl :: x:_ -> Prop {EQ x x}
@-}




{-@
invZLEN :: m:_ -> Prop {LE m zero} -> Prop {EQ m zero} @-}
invZLEN :: Nat -> LERule -> EQRule Nat
invZLEN _m (ZLEN m) = Refl m
