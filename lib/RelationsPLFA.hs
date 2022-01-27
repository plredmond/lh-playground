{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}


-- | Implementing some of https://plfa.github.io/Relations/
module RelationsPLFA where

import Language.Haskell.Liquid.ProofCombinators




-- * Detour to define nats

data Nat = Zero | Suc Nat

zero    = Zero      {-@ reflect zero  @-}
one     = Suc zero  {-@ reflect one   @-}
two     = Suc one   {-@ reflect two   @-}
three   = Suc two   {-@ reflect three @-}
four    = Suc three {-@ reflect four  @-}




-- * Continue with the Relations chapter

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




-- * Detour to define propositional equality

data EQProp a = EQ a a

data EQRule a where
    Refl :: a -> EQRule a
{-@
data EQRule a where
    Refl :: x:_ -> Prop {EQ x x}
@-}

{-@
eqReflexive :: x:_ -> Prop {EQ x x} @-}
eqReflexive :: a -> EQRule a
eqReflexive x = Refl x

-- | x≡y ⇔ y≡x
{-@
eqSymmetric₁ :: x:_ -> y:_ -> Prop {EQ x y} -> Prop {EQ y x} @-}
eqSymmetric₁ :: a -> a -> EQRule a -> EQRule a
eqSymmetric₁ _x _y xEQy@Refl{} = xEQy
{-@
eqSymmetric₂ :: x:_ -> y:_ -> Prop {EQ y x} -> Prop {EQ x y} @-}
eqSymmetric₂ :: a -> a -> EQRule a -> EQRule a
eqSymmetric₂ _x _y yEQx@Refl{} = yEQx

{-@
eqTransitive :: x:_ -> y:_ -> z:_ -> Prop {EQ x y} -> Prop {EQ y z} -> Prop {EQ x z} @-}
eqTransitive :: a -> a -> a -> EQRule a -> EQRule a -> EQRule a
eqTransitive _x _y _z xEQy@Refl{} _yEQz@Refl{} = xEQy




-- * Continue with the Relations chapter

-- | Invert the other rule to get propositional equality
{-@
invZLEN :: m:_ -> Prop {LE m zero} -> Prop {EQ m zero} @-}
invZLEN :: Nat -> LERule -> EQRule Nat
invZLEN _m (ZLEN m) = Refl m

-- | Invert the other rule to get SMT equality
{-@
invZLEN' :: m:_ -> Prop {LE m zero} -> {m == zero} @-}
invZLEN' :: Nat -> LERule -> Proof
invZLEN' _m (ZLEN __m) = ()




-- * Detour to show Propositional ⇔ SMT

-- ** Propositional equality ⇔ SMT equality

{-@
eqSMT₁ :: x:_ -> y:_ -> Prop {EQ x y} -> {x == y} @-}
eqSMT₁ :: a -> a -> EQRule a -> Proof
eqSMT₁ _x _y Refl{} = ()
{-@
eqSMT₂ :: x:_ -> y:_ -> {_:Proof | x == y} -> Prop {EQ x y} @-}
eqSMT₂ :: a -> a -> Proof -> EQRule a
eqSMT₂ x _y () = Refl x

-- ** Convert Nat to Integer

{-@ reflect natVal @-}
natVal :: Nat -> Integer
natVal Zero = 0
natVal (Suc n₀) = 1 + natVal n₀

{-@
natValNat :: n:_ -> { natVal zero <= natVal n
                   &&           0 <= natVal n } @-}
natValNat :: Nat -> Proof
natValNat Zero = 0 <= natVal zero *** QED
natValNat (Suc n₀)
    =   0 <= natVal (Suc n₀)
--  === 0 <= 1 + natVal n₀
    ? natValNat n₀
    *** QED

-- ** Propositional x≤y ⇔ SMT x≤y

{-@
leSMT₁ :: x:_ -> y:_ -> Prop {LE x y} -> {natVal x <= natVal y} @-}
leSMT₁ :: Nat -> Nat -> LERule -> Proof
leSMT₁ _x _y (ZLEN y) = natValNat y
leSMT₁ x y (SLES m n mLEn)
    = leSMT₁ m n mLEn
    ? (natVal x === 1 + natVal m)
    ? (natVal y === 1 + natVal n)
{-@
leSMT₂ :: x:_ -> y:_ -> {_:_ | natVal x <= natVal y} -> Prop {LE x y} @-}
leSMT₂ :: Nat -> Nat -> Proof -> LERule
leSMT₂ Zero y () = ZLEN y
leSMT₂ (Suc x₀) y () =
    case y ? sucLeNonZero x₀ y of
    Suc y₀ -> SLES x₀ y₀ (leSMT₂ x₀ y₀ (invSLES_SMT x₀ y₀))

-- *** Detour for awkward lemmas

-- | `Suc x ≤ y  ⇒  y ≠ zero` for Nats in SMT.
{-@
sucLeNonZero :: x:_ -> {y:_ | natVal (Suc x) <= natVal y} -> {y /= zero} @-}
sucLeNonZero :: Nat -> Nat -> Proof
sucLeNonZero _x (Suc _y₀) = () *** QED
sucLeNonZero x Zero
    =   natVal (Suc x) <= natVal zero
--  === 1 + natVal x <= 0
--  === natVal x <= (-1)
    ? natValNat x -- contradiction
    *** QED

-- | Inversion of s≤s for Nats, but in SMT.
{-@
invSLES_SMT :: m:_ -> {n:_ | natVal (Suc m) <= natVal (Suc n)} -> {natVal m <= natVal n} @-}
invSLES_SMT :: Nat -> Nat -> Proof
invSLES_SMT m n = natVal (Suc m) <= natVal (Suc n) *** QED




-- * Continue with the relations chapter

{-@
leRefl :: n:_ -> Prop {LE n n} @-}
leRefl :: Nat -> LERule
leRefl Zero = ZLEN zero
leRefl (Suc n₀) = SLES n₀ n₀ (leRefl n₀)




-- * Detour to do some random proof from the induction chapter

{-@ reflect plus @-}
plus :: Nat -> Nat -> Nat
plus Zero y = y
plus (Suc x) y = Suc (plus x y)

{-@ reflect suc @-}
suc :: Nat -> Nat
suc = Suc

{-@
eqCong :: f:_ -> x:_ -> y:_ -> Prop {EQ x y} -> Prop {EQ (f x) (f y)} @-}
eqCong :: (a -> b) -> a -> a -> EQRule a -> EQRule b
eqCong f _x _y (Refl x) = Refl (f x)

{-@
plusAssocJat :: x:_ -> y:_ -> z:_ -> Prop {EQ (plus (plus x y) z) (plus x (plus y z))} @-}
plusAssocJat :: Nat -> Nat -> Nat -> EQRule Nat
plusAssocJat Zero y z
    -- GOAL: (0+y)+z) = (0+(y+z)
    = Refl (plus y z)
    -- without PLE, you must additionally cause LH to see (0+) as an identity
    ? (plus zero y) -- === y
    ? (plus zero (plus y z)) -- === plus y z
plusAssocJat (Suc x₀) y z
    -- GOAL: (suc x₀+y)+z) = (suc x₀+(y+z)
    = eqCong suc (plus (plus x₀ y) z) (plus x₀ (plus y z)) (plusAssocJat x₀ y z)
    -- without PLE, you must additionally eval the goal to tha values passed to eqCong
    ? (plus (plus (suc x₀) y) z === plus (suc (plus x₀ y)) z === suc (plus (plus x₀ y) z))
    ? (plus (suc x₀) (plus y z) === suc (plus x₀ (plus y z)))

{-@ ple plusAssocJatPle @-}
{-@
plusAssocJatPle :: x:_ -> y:_ -> z:_ -> Prop {EQ (plus (plus x y) z) (plus x (plus y z))} @-}
plusAssocJatPle :: Nat -> Nat -> Nat -> EQRule Nat
plusAssocJatPle Zero y z
    -- GOAL: (0+y)+z) = (0+(y+z)
    = Refl (plus y z)
plusAssocJatPle (Suc x₀) y z
    -- GOAL: (suc x₀+y)+z) = (suc x₀+(y+z)
    = eqCong suc (plus (plus x₀ y) z) (plus x₀ (plus y z)) (plusAssocJatPle x₀ y z)

{-@
plusAssocEquational :: m:_ -> n:_ -> p:_ -> {plus (plus m n) p == plus m (plus n p)} @-}
plusAssocEquational :: Nat -> Nat -> Nat -> Proof
plusAssocEquational Zero n p
    =   plus (plus Zero n) p
    === plus n p
    === plus Zero (plus n p)
    *** QED
plusAssocEquational (Suc m₀) n p
    =   plus (plus (Suc m₀) n) p
    === plus (Suc (plus m₀ n)) p
    === Suc (plus (plus m₀ n) p)
        ? plusAssocEquational m₀ n p
    === Suc (plus m₀ (plus n p))
    === plus (Suc m₀) (plus n p)
    *** QED

{-@
plusAssocNative :: m:_ -> n:_ -> p:_ -> {(m + n) + p == m + (n + p)} @-}
plusAssocNative :: Int -> Int -> Int -> Proof
plusAssocNative m n p = () -- no PLE required
