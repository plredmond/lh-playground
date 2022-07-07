module AssocSetterPreservesOthers where

import Prelude hiding (tail, lookup, elem)

import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}

type Assoc k v = [(k, v)]

lookup :: Eq k => k -> Assoc k v -> Maybe v
lookup _key [] = Nothing
lookup key ((k,v):xs)
    | key == k = Just v
    | otherwise = lookup key xs
{-@ reflect lookup @-}

set :: Eq k => k -> v -> Assoc k v -> Assoc k v
set key val [] = [(key, val)]
set key val ((k,v):xs)
    | key == k = (k,val):xs
    | otherwise = (k,v):set key val xs
{-@ reflect set @-}

-- GOAL: Modify an element and prove that other elements aren't modified.
--
-- This is like the "* r" part of the frame rule.
--
--        { p } c { q }
--    ---------------------
--    { p * r } c { q * r }
--
-- p is "target account is n"
-- q is "target account is n + 5"
-- r is "all the other accounts don't change"

type Acct = String
type Money = Int
type State = Assoc Acct Money

-- Previous approach was something like:
--
-- delete
--      :: Acct -> State -> State
-- deleteModifiedAndGetEqualSets
--      ::    a:Acct
--      ->   s0:State
--      -> { s1:State | s1 == transition s0 }
--      -> {  _:Proof | delete a s0 == delete a s1 }

giveMoney :: Acct -> State -> State
giveMoney acct st =
    case lookup acct st of
        Nothing -> set acct 5 st
        Just val -> set acct (val + 5) st
{-@ reflect giveMoney @-}

{-@
giveMoneyPreservesOthers
    ::    a:Acct
    ->   s0:State
    -> {  b:Acct | a /= b }
    -> { lookup b s0 == lookup b (giveMoney a s0) }
@-}
giveMoneyPreservesOthers :: Acct -> State -> Acct -> Proof
giveMoneyPreservesOthers a s₀ b =
    -- by cases of giveMoney (which calls lookup)
    case lookup a s₀ of
        Nothing ->
                lookup b (giveMoney a s₀)
            === lookup b (set a 5 s₀)
                ? setPreservesOthers a 5 s₀ b
            *** QED
        Just val ->
                lookup b (giveMoney a s₀)
            === lookup b (set a (val + 5) s₀)
                ? setPreservesOthers a (val + 5) s₀ b
            *** QED

-- |
--
-- Premise:
--
-- a /= b
--
-- Cases:
--
-- lookup b (set a val [])         -- Set prepends head, and lookup searches (empty) tail. -- Lookup returns Nothing in either case.
-- lookup b (set a val ((a,_):xs)) -- Set replaces head, and lookup searches tail.         -- Lookup searches the /same/ tail in either case.
-- lookup b ((b,v):set a val xs)   -- Set searches tail, and lookup returns head.          -- Lookup returns the /same/ head in either case.
-- lookup b ((k,v):set a val xs)   -- Both set and lookup search the tail.                 -- Inductive step
--
{-@
setPreservesOthers
    ::    a:k
    ->  val:v
    ->  xxs:Assoc k v
    -> {  b:k | a /= b }
    -> { lookup b xxs == lookup b (set a val xxs) }
@-}
setPreservesOthers :: Eq k => k -> v -> Assoc k v -> k -> Proof
setPreservesOthers a val xxs b =
    let
    -- setCases could be inlined as the body of setPreservesOthers if you wanted
    setCases =
      case xxs of
        [] ->
                lookup b (set a val xxs) -- restate right side of conclusion
            === lookup b (set a val [])  -- xxs == []
            === lookup b [(a, val)]      -- def of set
                -- lookup case for [] is excluded by `xxs==[(a,val)]`
                -- lookup case for `key==k` is excluded by premise `a/=b`
            === lookup b []  -- def of lookup
            === Nothing      -- def of lookup again
            === lookup b xxs -- obtain left side of conclusion (recall `xxs==[]`)
                -- WHY? `set` added `a` to empty-assoc `xxs`, but `a/=b` means
                -- `lookup b` was `Nothing` both before and after
            *** QED
        (k,v):xs
            | a == k ->
                    lookup b (set a val xxs)        -- restate right side of conclusion
                === lookup b (set a val ((a,v):xs)) -- xxs == (k,v):xs && a == k
                === lookup b ((a,val):xs)           -- def of set
                    -- lookup case for [] is excluded by `xxs=(a,val):xs`
                    -- lookup case for `key==k` is excluded by premise `a/=b`
                === lookup b xs  -- def of lookup
                === lookup b xxs -- obtain left side of conclusion
                    -- WHY? `set` replaced pair at head of `xxs`, but `a/=b`
                    -- means `lookup b` recurses past the head to the tail of
                    -- `xxs`, both before and after (congruency)
                *** QED
            | otherwise ->
                    lookup b (set a val xxs)        -- restate right side of conclusion
                === lookup b (set a val ((k,v):xs)) -- xxs == (k,v):xs
                === lookup b ((k,v):set a val xs)   -- def of set && a /= k
                    -- lookup case for [] is excluded by `xxs=(k,v):xs`
                    ? lookupCases ((k,v):xs)
                *** QED
    -- lookupCases gets an inferred type that its arg is a nonempty list and `a /= k`
    lookupCases ((k,v):xs)
        | b == k =
                lookup b ((k,v):set a val xs) -- restate evidince from callsite of lookupCases
            === Just v                        -- def of lookup && b == k
            === lookup b xxs                  -- obtain left side of conclusion
                -- WHY? `set` recurses past the head of `xxs` but `lookup`
                -- returns the value at the head
            *** QED
        | otherwise =
                lookup b ((k,v):set a val xs) -- restate evidence from callsite of lookupCases
            === lookup b (set a val xs)       -- def of lookup && b /= k
                ? setPreservesOthers a val xs b -- apply induction hypothesis
            === lookup b xs                   -- left side of induction hypothesis
            === lookup b xxs                  -- obtain left side of conclusion
                -- WHY? `set` recurses past the head of `xxs` and so does
                -- `lookup`; we rely on the induction hypothesis and congruency
            *** QED
    in
    setCases
