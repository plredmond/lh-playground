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
-- induction on the input x in `Step x`.
{-@
stepDeterministic_ind_x :: Deterministic {Step} @-}
stepDeterministic_ind_x :: TM -> TM -> TM -> StepRule -> StepRule -> Proof

stepDeterministic_ind_x TRU     _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x FLS     _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x TEST{}  _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x ZRO     _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x SCC{}   _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x PRD{}   _y??? _y??? _xRy??? _xRy??? = () *** Admit
stepDeterministic_ind_x ISZRO{} _y??? _y??? _xRy??? _xRy??? = () *** Admit

-- | Proof that `Step` is deterministic in the inductive proposition style via
-- induction on the rules.
{-@
stepDeterministic_ind_xRy??? :: Deterministic {Step} @-}
stepDeterministic_ind_xRy??? :: TM -> TM -> TM -> StepRule -> StepRule -> Proof

stepDeterministic_ind_xRy??? _x _y??? _y??? (TestTru _t??? _t???) (Test __t??? __t???' __t??? __t??? __t???Rt???') = () *** Admit -- case must be completed
stepDeterministic_ind_xRy??? _x _y??? _y??? TestTru{} TestTru{} = trivial -- case can be deleted
stepDeterministic_ind_xRy??? _x _y??? _y??? TestTru{} Scc{} = impossible "" -- case can be deleted
stepDeterministic_ind_xRy??? _x _y??? _y??? TestTru{} _xRy??? = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? TestFls{}  Test{}     = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? TestFls{}  _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? Test{}     TestTru{}  = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Test{}     TestFls{}  = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Test{}     Test{}     = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Test{}     _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? Scc{}      Scc{}      = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Scc{}      _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? PrdZro{}   Prd{}      = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? PrdZro{}   _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? PrdScc{}   Prd{}      = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? PrdScc{}   _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? Prd{}      PrdZro{}   = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Prd{}      PrdScc{}   = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Prd{}      Prd{}      = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Prd{}      _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? IszroZro{} Iszro{}    = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? IszroZro{} _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? IszroScc{} Iszro{}    = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? IszroScc{} _xRy???      = ()

stepDeterministic_ind_xRy??? _x _y??? _y??? Iszro{}    IszroZro{} = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Iszro{}    IszroScc{} = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Iszro{}    Iszro{}    = () *** Admit
stepDeterministic_ind_xRy??? _x _y??? _y??? Iszro{}    _xRy???      = ()




-- * Try defining operational semantics as a function instead of an inductive proposition

-- QQQ It's awkward to define step as a function because it is partial.
{-@ reflect stepf @-}
stepf :: TM -> Maybe TM
stepf = \case
    TEST TRU  t??? _t???                    -> Just $ t???
    TEST FLS _t???  t???                    -> Just $ t???
    TEST _t???@(stepf -> Just t???') t??? t???  -> Just $ TEST t???' t??? t???
    SCC _t???@(stepf -> Just t???')         -> Just $ SCC t???'
    PRD ZRO                             -> Just $ ZRO
    PRD (SCC v) | nValue v              -> Just $ v
    PRD _t???@(stepf -> Just t???')         -> Just $ PRD t???'
    ISZRO ZRO                           -> Just $ TRU
    ISZRO (SCC v) | nValue v            -> Just $ FLS
    ISZRO _t???@(stepf -> Just t???')       -> Just $ ISZRO t???'
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
congruence _f _x _y??? _y??? = ()

{-@
stepDeterministicf :: Deterministicf {stepf} @-}
stepDeterministicf :: TM -> Maybe TM -> Maybe TM -> Proof
stepDeterministicf = congruence stepf
-- QQQ It is pointless to try to write down a proof of determinism of the
-- stepf function because determinism is already part of LH's model of
-- Haskell.
