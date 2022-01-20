{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-@ LIQUID "--reflection" @-}
module ModelNatsWithInts where

import Language.Haskell.Liquid.ProofCombinators

-- Represent the naturals with the integers

type T = Integer

{-@ reflect t0 @-}
t0 :: T
t0 = 0

-- | `a → b` in one step.
data ArithProp = OneStepTo T T

data ArithRule where
    Add :: T -> Integer -> ArithRule
    Sub :: T -> Integer -> ArithRule
{-@
data ArithRule where
    Add :: m:_ -> {n:_ | 0 <= n} -> Prop {OneStepTo m (m + n)}
    Sub :: m:_ -> {n:_ | 0 <= n && n <= m} -> Prop {OneStepTo m (m - n)}
@-}

-- | `a →* b` in N steps.
data TRCProp = NStepsTo T T

data TRCRule where
    Lift :: T -> T -> ArithRule -> TRCRule
    Refl :: T -> TRCRule
    Trans :: T -> T -> T -> TRCRule -> TRCRule -> TRCRule
{-@
data TRCRule where
    Lift :: m:_ -> n:_ -> Prop {OneStepTo m n} -> Prop {NStepsTo m n}
    Refl :: m:_ -> Prop {NStepsTo m m}
    Trans :: m:_ -> n:_ -> p:_ -> Prop {NStepsTo m n} -> Prop {NStepsTo n p} -> Prop {NStepsTo m p}
@-}

{-@ type Reachable N = Prop {NStepsTo t0 N} @-}

{-@
prop :: n:_ -> Reachable {n} -> {0 <= n} @-}
prop :: T -> TRCRule -> Proof
prop n zNSTn = prop_star t0 n zNSTn

-- | You can conclude `0 ≤ t0`.
{-@
prop_0 :: {0 <= t0} @-}
prop_0 :: Proof
prop_0 = ()
-- NOTE: This proof is unused. If it were used, it would be adding info about
-- t0 in the definition of `prop`, as in the Agda version.

-- ===
-- NOTE: In all the code above, we go m→n, but the mnemonic swaps to n→m below.

-- | If you know `0 ≤ n` and `n → m` then you can conclude `0 ≤ m`.
{-@
prop_n :: {n:_ | 0 <= n} -> m:_ -> Prop {OneStepTo n m} -> {0 <= m} @-}
prop_n :: T -> T -> ArithRule -> Proof
prop_n _n _m Add{} = () -- SMT proves without PLE
prop_n _n _m Sub{} = () -- SMT proves without PLE

-- | If you know `0 ≤ n` and `n →* m` then you can conclude `0 ≤ m`.
{-@
prop_star :: {n:_ | 0 <= n} -> m:_ -> Prop {NStepsTo n m} -> {0 <= m} @-}
prop_star :: T -> T -> TRCRule -> Proof
prop_star _n _m (Lift n m nOSTm) = prop_n n m nOSTm
prop_star _n _m Refl{} = () -- SMT proves without PLE
prop_star _n _m (Trans n m p nNSTm mNSTp) = prop_star (m ? prop_star n m nNSTm) p mNSTp
-- NOTE: This last line is notable because it has all the same pieces as the
-- Agda version, except the evidence that `0 ≤ m` is added to the context of
-- `m` with `?` instead of being a separate argument.



-- * Original Agda code

{-

module trivtransys where

import Data.Nat.Base
open import Data.Integer using (ℤ; 0ℤ; _≤_; _+_; _-_; -_)
open import Data.Integer.Properties as ℤₚ

-- Model the ts with the ints

t : Set
t = ℤ

t₀ : t
t₀ = 0ℤ


data _➡_ : t → t → Set where

  add : ∀ {m : t} {n : ℤ}
    → 0ℤ ≤ n
      ---------
    → m ➡ (m + n)

  sub : ∀ {m : t} {n : ℤ}
    → 0ℤ ≤ n → n ≤ m
      ---------------
    → m ➡ (m - n)


data _➡*_ : t -> t -> Set where

  lift : ∀ {m n : t}
    → m ➡ n
      ------
    → m ➡* n

  refl : ∀ {m : t}
      ------
    → m ➡* m

  trans : ∀ {m n p : t}
    → m ➡* n → n ➡* p
      ---------------
    → m ➡* p


reachable : t -> Set
reachable n = t₀ ➡* n

prop : ∀ n → reachable n → 0ℤ ≤ n
prop _ x = prop* _ _ prop₀ x
  where
  prop₀ : 0ℤ ≤ t₀
  prop₀ = _≤_.+≤+ Data.Nat.Base._≤_.z≤n

  propₙ : ∀ (n m : t) → 0ℤ ≤ n → n ➡ m → 0ℤ ≤ m
  propₙ n m p (add x)   = ℤₚ.+-mono-≤ p x
  propₙ n m p (sub x y) = ℤₚ.m≤n⇒0≤n-m y

  prop* : ∀ (n m : t) → 0ℤ ≤ n → n ➡* m → 0ℤ ≤ m
  prop* n m Pn (lift x)    = propₙ _ _ Pn x
  prop* n .n Pn refl       = Pn
  prop* n m Pn (trans x y) = prop* _ _ (prop* _ _ Pn x) y
-}
