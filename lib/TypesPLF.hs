{-@ LIQUID "--reflection" @-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

-- | <https://softwarefoundations.cis.upenn.edu/plf-current/Types.html>
module TypesPLF where

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

-- QQQ It's awkward to define step as a function because it is partial.

{-@ reflect step @-}
step :: TM -> Maybe TM
step = \case
    TEST TRU  t₁ _t₂                    -> Just $ t₁
    TEST FLS _t₁  t₂                    -> Just $ t₂
    TEST _t₁@(step -> Just t₁') t₂ t₃   -> Just $ TEST t₁' t₂ t₃
    SCC _t₁@(step -> Just t₁')          -> Just $ SCC t₁'
    PRD ZRO                             -> Just $ ZRO
    PRD (SCC v) | nValue v              -> Just $ v
    PRD _t₁@(step -> Just t₁')          -> Just $ PRD t₁'
    ISZRO ZRO                           -> Just $ TRU
    ISZRO (SCC v) | nValue v            -> Just $ FLS
    ISZRO _t₁@(step -> Just t₁')        -> Just $ ISZRO t₁'
    _                                   -> Nothing

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

{-@ type Stuck' = {t:_ | not (value t) && step t == Nothing} @-}

{-@
someTermIsStuck' :: Stuck' @-}
someTermIsStuck' :: TM
someTermIsStuck' = SCC TRU ? normalForm
  where
    {-@ normalForm :: { step (SCC TRU) == Nothing } @-}
    normalForm
        =   step (SCC TRU)
        === case step TRU of Nothing -> Nothing
        === Nothing
        *** QED
    -- QQQ The evaluation from `step (SCC TRU)` to `case step TRU` comes from
    -- use of view patterns in `step`. The `Nothing -> Nothing` means that if
    -- the view pattern doesn't match then the whole pattern fails.

{-@
valueIsNf :: {t:_ | value t} -> NormalForm {Step} {t} @-}
valueIsNf :: TM -> TM -> StepRule -> Proof
valueIsNf TRU   _t' Iszro{} = () -- No rules apply (match on Iszro to prompt totally checker to see no cases apply)
valueIsNf FLS   _t' Iszro{} = () -- No rules apply
valueIsNf ZRO   _t' Iszro{} = () -- No rules apply
valueIsNf SCC{} _t' (Scc u u' u2u') = valueIsNf u u' u2u'

{-@
valueIsNf' :: {t:_ | value t} -> { step t == Nothing } @-}
valueIsNf' :: TM -> Proof
valueIsNf' = \case
    TRU -> step TRU *** QED -- No pattern matches, evaluates to Nothing
    FLS -> step FLS *** QED -- No pattern matches, evaluates to Nothing
    ZRO -> step ZRO *** QED -- No pattern matches, evaluates to Nothing
    SCC t | nValue t -> step (SCC t) ? valueIsNf' t *** QED
    -- QQQ The only case where `step` might do work is for `SCC t`, but since
    -- the precondition mandates `nValue t` we can use the inductive
    -- assumption that `step t` is `Nothing`, which guarantees the `SCC t` case
    -- in `step` won't match.
