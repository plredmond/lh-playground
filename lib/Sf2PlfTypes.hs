{-@ LIQUID "--reflection" @-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

-- | <https://softwarefoundations.cis.upenn.edu/plf-current/Types.html>
module Sf2PlfTypes where

import Language.Haskell.Liquid.ProofCombinators

data TM where
    TRU :: TM
    FLS :: TM
    TEST :: TM -> TM -> TM -> TM
    ZRO :: TM
    SCC :: TM -> TM
    PRD :: TM -> TM
    ISZRO :: TM -> TM

-- QQQ Defining bValue and nValue and value as inductive
-- propositions is a pain and so we use functions.

{-@ measure bValue @-}
bValue :: TM -> Bool
bValue TRU = True
bValue FLS = True
bValue _ = False

{-@ measure nValue @-}
nValue :: TM -> Bool
nValue ZRO = True
nValue (SCC t) = nValue t
nValue _ = False

{-@ inline value @-}
value :: TM -> Bool
value t = bValue t || nValue t

-- QQQ Defining step as an inductive proposition requires three definitions.
--
-- BUG Using `Prop` with binder `v` runs into the type aliases name
-- collision bug b/c liquid-prelude defines `Prop` using binder `v`.
--
-- QQQ Since we define value/nValue/bValue with functions, for the nValue
-- premises, we use LH/SMT evidence. For Step premises, we use inductive
-- proposition arguments.

data StepProp where
    Step :: TM -> TM -> StepProp

data StepRule where
    TestTru  :: TM -> TM -> StepRule
    TestFls  :: TM -> TM -> StepRule
    Test     :: TM -> TM -> TM -> TM -> StepRule -> StepRule
    Scc      :: TM -> TM -> StepRule -> StepRule
    PrdZro   :: StepRule
    PrdScc   :: TM -> StepRule
    Prd      :: TM -> TM -> StepRule -> StepRule
    IszroZro :: StepRule
    IszroScc :: TM -> StepRule
    Iszro    :: TM -> TM -> StepRule -> StepRule
{-@
data StepRule where
    TestTru  :: t1:_ -> t2:_
             -> Prop{ Step (TEST TRU t1 t2) t1 }
    TestFls  :: t1:_ -> t2:_
             -> Prop{ Step (TEST FLS t1 t2) t2 }
    Test     :: t1:_ -> t1':_ -> t2:_ -> t3:_
             -> Prop{ Step t1 t1' }
             -> Prop{ Step (TEST t1 t2 t3) (TEST t1' t2 t3) }
    Scc      :: t1:_ -> t1':_
             -> Prop{ Step t1 t1' }
             -> Prop{ Step (SCC t1) (SCC t1') }
    PrdZro   :: Prop{ Step (PRD ZRO) ZRO }
    PrdScc   :: {n:_ | nValue n}
             -> Prop{ Step (PRD (SCC n)) n }
    Prd      :: t1:_ -> t1':_
             -> Prop{ Step t1 t1' }
             -> Prop{ Step (PRD t1) (PRD t1') }
    IszroZro :: Prop{ Step (ISZRO ZRO) TRU }
    IszroScc :: {n:_ | nValue n}
             -> Prop{ Step (ISZRO (SCC n)) FLS }
    Iszro    :: t1:_ -> t1':_
             -> Prop{ Step t1 t1' }
             -> Prop{ Step (ISZRO t1) (ISZRO t1') }
@-}

{-@ type Value    T = {t:_ | t == T &&      value T } @-}
{-@ type NotValue T = {t:_ | t == T && not (value T)} @-}

{-@ type NormalForm R T = t':_ -> Prop{ R T t' } -> {_:Proof | false} @-}
{-@ type Stuck T = (NotValue {T}, NormalForm {Step} {T}) @-}

{-@ type Deterministic R
        = x:_ -> y1:_ -> y2:_ -> Prop{ R x y1 } -> Prop{ R x y2 }
        -> {_:Proof | y1 == y2} @-}

{-@
someTermIsStuck :: Stuck {SCC TRU} @-}
someTermIsStuck :: (TM, TM -> StepRule -> Proof)
someTermIsStuck = (notValue, normalForm)
  where
    {-@ notValue :: NotValue {SCC TRU} @-}
    notValue = SCC TRU -- LH figures out `not (value (SCC TRU))`.

    {-@ normalForm :: NormalForm {Step} {SCC TRU} @-}
    normalForm :: TM -> StepRule -> Proof
    normalForm _t' (Scc TRU _tru' Iszro{}) = ()
    -- QQQ Only the `Scc` rule is applicable to `SCC TRU`. However no rule is
    -- applicable to `TRU` and so we match arbitrarily on `Iszro{}` and LH
    -- accepts that nothing further is required.

{-@
valueIsNf :: {t:_ | value t} -> NormalForm {Step} {t} @-}
valueIsNf :: TM -> TM -> StepRule -> Proof
valueIsNf TRU   _t' Iszro{} = () -- No rules apply (match on Iszro to prompt totally checker to see no cases apply)
valueIsNf FLS   _t' Iszro{} = () -- No rules apply
valueIsNf ZRO   _t' Iszro{} = () -- No rules apply
valueIsNf SCC{} _t' (Scc u u' u2u') = valueIsNf u u' u2u'

-- | Binder for a proof that `Step` is deterministic; used only for looking at
-- the LH context/vim-annotations.
{-@
stepDeterministic :: Deterministic {Step} @-}
stepDeterministic :: TM -> TM -> TM -> StepRule -> StepRule -> Proof
stepDeterministic = undefined

-- | Proof that `Step` is deterministic in the inductive proposition style via
-- induction on the rules.
{-@
stepDeterministic_ind_xRy₁ :: Deterministic {Step} @-}
stepDeterministic_ind_xRy₁ :: TM -> TM -> TM -> StepRule -> StepRule -> Proof

stepDeterministic_ind_xRy₁ _x _y₁ _y₂ _xRy₁ _xRy₂ = () *** Admit

-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestTru{} _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestFls{} _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Test{}    _xRy₂ = () *** Admit

-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestTru{}  TestTru{} = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestTru{}  __DEFAULT = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestFls{}  _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Test{}     _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Scc{}      _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdZro{}   _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdScc{}   _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Prd{}      _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroZro{} _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroScc{} _xRy₂ = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Iszro{}    _xRy₂ = () *** Admit

-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestTru{}  TestTru{}  = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestTru{}  Test{}     = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestFls{}  TestFls{}  = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ TestFls{}  Test{}     = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Test{}     TestTru{}  = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Test{}     TestFls{}  = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Test{}     Test{}     = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Scc{}      Scc{}      = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdZro{}   PrdZro{}   = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdZro{}   Prd{}      = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdScc{}   PrdScc{}   = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ PrdScc{}   Prd{}      = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Prd{}      PrdZro{}   = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Prd{}      PrdScc{}   = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Prd{}      Prd{}      = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroZro{} IszroZro{} = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroZro{} Iszro{}    = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroScc{} IszroScc{} = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ IszroScc{} Iszro{}    = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Iszro{}    IszroZro{} = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Iszro{}    IszroScc{} = () *** Admit
-- stepDeterministic_ind_xRy₁ _x _y₁ _y₂ Iszro{}    Iszro{}    = () *** Admit

-- See "potential followup" in the PR:
-- https://github.com/ucsd-progsys/liquidhaskell/pull/2045










































-- * Try defining operational semantics as a function instead of an inductive proposition

-- QQQ It's awkward to define step as a function because it is partial.
{-@ reflect stepf @-}
stepf :: TM -> Maybe TM
stepf = \case
    TEST TRU  t₁ _t₂                    -> Just $ t₁
    TEST FLS _t₁  t₂                    -> Just $ t₂
    TEST _t₁@(stepf -> Just t₁') t₂ t₃  -> Just $ TEST t₁' t₂ t₃
    SCC _t₁@(stepf -> Just t₁')         -> Just $ SCC t₁'
    PRD ZRO                             -> Just $ ZRO
    PRD (SCC v) | nValue v              -> Just $ v
    PRD _t₁@(stepf -> Just t₁')         -> Just $ PRD t₁'
    ISZRO ZRO                           -> Just $ TRU
    ISZRO (SCC v) | nValue v            -> Just $ FLS
    ISZRO _t₁@(stepf -> Just t₁')       -> Just $ ISZRO t₁'
    _                                   -> Nothing

-- | Same meaning as Stuck?
{-@ type Stuckf = {t:_ | not (value t) && stepf t == Nothing} @-}

-- | Same meaning as Deterministic?
{-@ type Deterministicf Rf
        = x:_ -> {y1:_ | Rf x == y1} -> {y2:_ | Rf x == y2}
        -> {_:Proof | y1 == y2} @-}

{-@
someTermIsStuckf :: Stuckf @-}
someTermIsStuckf :: TM
someTermIsStuckf = SCC TRU ? normalForm
  where
    {-@ normalForm :: { stepf (SCC TRU) == Nothing } @-}
    normalForm
        =   stepf (SCC TRU)
        === case stepf TRU of Nothing -> Nothing
        === Nothing
        *** QED
    -- QQQ The evaluation from `stepf (SCC TRU)` to `case stepf TRU` comes from
    -- use of view patterns in `stepf`. The `Nothing -> Nothing` means that if
    -- the view pattern doesn't match then the whole pattern fails.

{-@
valueIsNFf :: {t:_ | value t} -> { stepf t == Nothing } @-}
valueIsNFf :: TM -> Proof
valueIsNFf = \case
    TRU -> stepf TRU *** QED -- No pattern matches, evaluates to Nothing
    FLS -> stepf FLS *** QED -- No pattern matches, evaluates to Nothing
    ZRO -> stepf ZRO *** QED -- No pattern matches, evaluates to Nothing
    SCC t | nValue t -> stepf (SCC t) ? valueIsNFf t *** QED
    -- QQQ The only case where `stepf` might do work is for `SCC t`, but since
    -- the precondition mandates `nValue t` we can use the inductive
    -- assumption that `stepf t` is `Nothing`, which guarantees the `SCC t` case
    -- in `stepf` won't match.

-- | FIXME: Not exactly congruence, but something like it.
{-@
congruence :: f:_ -> Deterministicf {f} @-}
congruence :: (a -> b) -> a -> b -> b -> Proof
congruence _f _x _y₁ _y₂ = ()

{-@
stepDeterministicf :: Deterministicf {stepf} @-}
stepDeterministicf :: TM -> Maybe TM -> Maybe TM -> Proof
stepDeterministicf = congruence stepf
-- QQQ It is pointless to try to write down a proof of determinism of the
-- stepf function because determinism is already part of LH's model of
-- Haskell.
