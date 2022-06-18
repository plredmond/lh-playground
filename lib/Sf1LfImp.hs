{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data" @-}
{-@ LIQUID "--ple-local" @-}
{-# LANGUAGE LambdaCase #-}

-- | https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
module Sf1LfImp where

import Language.Haskell.Liquid.ProofCombinators

data AExp
    = ANum Int
    | APlus  AExp AExp
    | AMinus AExp AExp
    | AMult  AExp AExp -- *X is ×

data BExp
    = BTrue
    | BFalse
    | BEq  AExp AExp
    | BLe  AExp AExp -- =< is ≤
    | BNot BExp      -- NO is ¬
    | BAnd BExp BExp

{-@ reflect aeval @-}
aeval :: AExp -> Int
aeval = \case
    ANum   n     -> n
    APlus  a₁ a₂ -> aeval a₁ + aeval a₂
    AMinus a₁ a₂ -> aeval a₁ - aeval a₂
    AMult  a₁ a₂ -> aeval a₁ * aeval a₂

{-@ reflect beval @-}
beval :: BExp -> Bool
beval = \case
    BTrue      -> True
    BFalse     -> False
    BEq  a₁ a₂ -> aeval a₁ == aeval a₂
    BLe  a₁ a₂ -> aeval a₁ <= aeval a₂
    BNot b₁    -> not (beval b₁)
    BAnd b₁ b₂ -> beval b₁ && beval b₂

{-@ reflect optimize_0plus @-}
optimize_0plus :: AExp -> AExp
optimize_0plus = \case
    ANum   n     -> ANum n
    APlus  (ANum 0) e₂ -> optimize_0plus e₂
    APlus  e₁ e₂ -> optimize_0plus e₁ `APlus`  optimize_0plus e₂
    AMinus e₁ e₂ -> optimize_0plus e₁ `AMinus` optimize_0plus e₂
    AMult  e₁ e₂ -> optimize_0plus e₁ `AMult`  optimize_0plus e₂

{-@ ple optimize_0plus_sound @-}
{-@
optimize_0plus_sound :: a:_ -> {aeval (optimize_0plus a) == aeval a} @-}
optimize_0plus_sound :: AExp -> Proof
optimize_0plus_sound a = case a of
    ANum  _n     -> ()
--  APlus  (ANum 0) a₂ -> optimize_0plus_sound a₂ -- "interesting case"
    APlus  a₁ a₂ -> optimize_0plus_sound a₁ &&& optimize_0plus_sound a₂
    AMinus a₁ a₂ -> optimize_0plus_sound a₁ &&& optimize_0plus_sound a₂
    AMult  a₁ a₂ -> optimize_0plus_sound a₁ &&& optimize_0plus_sound a₂

data AEvalRProp = AExp :==> Int
{-@ infixr 4 :==> @-}
data AEvalRRule
    = E_ANum   Int
    | E_APlus  AExp AExp Int Int AEvalRRule AEvalRRule
    | E_AMinus AExp AExp Int Int AEvalRRule AEvalRRule
    | E_AMult  AExp AExp Int Int AEvalRRule AEvalRRule
{-@
data AEvalRRule where
    E_ANum :: n:_ ->
        Prop{ ANum n :==> n }
    E_APlus :: e1:_ -> e2:_ -> n1:_ -> n2:_ ->
        Prop{ e1 :==> n1 } ->
        Prop{ e2 :==> n2 } ->
        Prop{ APlus e1 e2 :==> n1 + n2 }
    E_AMinus :: e1:_ -> e2:_ -> n1:_ -> n2:_ ->
        Prop{ e1 :==> n1 } ->
        Prop{ e2 :==> n2 } ->
        Prop{ AMinus e1 e2 :==> n1 - n2 }
    E_AMult :: e1:_ -> e2:_ -> n1:_ -> n2:_ ->
        Prop{ e1 :==> n1 } ->
        Prop{ e2 :==> n2 } ->
        Prop{ AMult e1 e2 :==> n1 * n2 }
@-}

-- Ex: write beval rules out

{-@
aeval_iff_AEvalR₁ :: a:_ -> n:_ -> Prop{ a :==> n } -> {aeval a == n} @-}
aeval_iff_AEvalR₁ :: AExp -> Int -> AEvalRRule -> Proof
aeval_iff_AEvalR₁ a n aRn = case aRn of
    _ -> () *** Admit

{-@
aeval_iff_AEvalR₂ :: a:_ -> n:_ -> {_:_ | aeval a == n} -> Prop{ a :==> n } @-}
aeval_iff_AEvalR₂ :: AExp -> Int -> Proof -> AEvalRRule
aeval_iff_AEvalR₂ a n aRn = case aRn of
    _ -> undefined

-- TODO: Excercise (bevalR): Write a relation bevalR in the same style as
-- aevalR, and prove that it is equivalent to beval. 

-- WHY?  To do the Hoare logic chapters, need to first complete IMP, b/c
-- Hoare logic is about IMP.
