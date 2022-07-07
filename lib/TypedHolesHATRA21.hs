-- | Video of the talk is <https://www.youtube.com/watch?v=kd8cerjyjH4>
module TypedHolesHATRA21 where

import Prelude hiding (tail, lookup, elem)

import Language.Haskell.Liquid.ProofCombinators




-- | Normal tail function is partial.
tail :: [a] -> [a]
tail (_:xs) = xs
tail [] = undefined

-- | Refinement type prevents partial case in tail2.
{-@ tail2 :: {xs:[a] | xs /= []} -> {ys:[a] | len xs - 1 == len ys} @-}
tail2 :: [a] -> [a]
tail2 (_:xs) = xs




-- | OrdPair has a data refinement that `fir` is less than `sec`.
data OrdPair a = OrdPair a a
{-@
data OrdPair a = OrdPair
    { fir :: a
    , sec :: {s:a | fir < s}
    }
@-}

-- OrdPair2 is a type alias that uses the LH built-in abstract-refinement on
-- tuples and a lambda function to constrain `fst` to be less than `snd`.
{-@
type OrdPair2 a = (a, a)<{ \x y -> x < y }>
@-}




{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
elem _t [] = False
elem t (x:xs) = t == x || elem t xs

{-@
elemNotHeadInTail
    ::   t : a
    -> {xs : [a] | elem t xs && xs /= [] && t /= head xs}
    -> { _ : Proof | elem t (tail xs) }
@-}
elemNotHeadInTail :: Eq a => a -> [a] -> Proof
elemNotHeadInTail t (y:ys)
    =   elem t (y:ys)         -- Restate premise
    === (t == y || elem t ys) -- Expand; one must hold
--      ? t /= head (y:ys)    -- Another premise
--  === elem t ys             -- Conclusion
    *** QED




type Assoc k v = [(k, v)]

-- | Normal lookup function is partial, and returns a maybe.
lookup :: Eq k => k -> Assoc k v -> Maybe v
lookup key [] = Nothing
lookup key ((k,v):xs)
    | key == k = Just v
    | otherwise = lookup key xs

-- Reflection is required to lift hasKey to LH.
{-@ LIQUID "--reflection" @-}

-- | Predicate: Does the association contain the key?
{-@ reflect hasKey @-}
hasKey :: Eq k => k -> Assoc k v -> Bool
hasKey _key          [] = False
hasKey  key ((k,_v):xs) = key == k || hasKey key xs

-- | Refinement type prevents the case returning a maybe in lookup2.
{-@ lookup2 :: key:k -> {xs:Assoc k v | hasKey key xs} -> v @-}
lookup2 :: Eq k => k -> Assoc k v -> v
lookup2 key ((k,v):xs)
    | key == k = v
    | otherwise = lookup2 key xs

-- PLE-local is required to check lookup2.
{-@ LIQUID "--ple-local" @-}
{-@ ple lookup2 @-}

-- | Manually prove that hasKey implies the association is non-empty.
{-@ hasKeyImpliesNonEmpty :: key:k -> {xs:Assoc k v | hasKey key xs} -> { len xs > 0 } @-}
hasKeyImpliesNonEmpty :: Eq k => k -> Assoc k v -> Proof
hasKeyImpliesNonEmpty key [] =
        hasKey key [] -- Restate the premise
    *** QED -- Premise failed
hasKeyImpliesNonEmpty key ((k,v):xs) =
        () -- We just pattern-matched on it
    *** QED

-- | Manually prove that hasKey and the key not being at the head implies it is
-- in the tail.
{-@ hasKeyNotHeadImpliesTail :: key:k -> {xs:Assoc k v | hasKey key xs && len xs > 0 && key /= fst (head xs)} -> { hasKey key (tail xs) } @-}
hasKeyNotHeadImpliesTail :: Eq k => k -> Assoc k v -> Proof
hasKeyNotHeadImpliesTail key ((k,v):xs) =
        hasKey key ((k,v):xs)       -- Restate the premise
    === (key == k || hasKey key xs) -- Expand the premise; one of these must be true
        ? key /= k                  -- This is also a premise
    === hasKey key xs               -- The other must be true
    *** QED

-- | Refinement type prevents the case returning a maybe in lookup3. No PLE is
-- needed because of the explicit proofs.
{-@ lookup3 :: key:k -> {xs:Assoc k v | hasKey key xs} -> v @-}
lookup3 :: Eq k => k -> Assoc k v -> v
lookup3 key assoc = case assoc ? hasKeyImpliesNonEmpty key assoc of
    (k,v):xs
        | key == k -> v
        | otherwise -> lookup3 key (xs ? hasKeyNotHeadImpliesTail key assoc)




{-
ASIDE: You could define an empty list as:

    empty1 xs = xs == []

    But empty1 imposes an equality constraint on the list content.

    empty2 xs = case xs of
        [] -> True
        (_:_) -> False

    But empty2 requires your own definition.

    empty3 xs = len xs > 0

    But empty3 relies on the LH built-in "len".

In any case, make sure you're consistent with the definition you choose.
-}




{-@ reflect insert @-}
insert :: Eq k => k -> v -> Assoc k v -> Assoc k v
insert key val [] = (key,val):[]
insert key val ((k,v):xs)
    | key == k = (key,val):xs
    | otherwise = (k,v):insert key val xs

-- | Manually prove that after performing an insert the result has the key.
{-@
prop1
    :: key:k -> val:v -> xs:Assoc k v
    -> { _:Proof | hasKey key (insert key val xs) }
@-}
prop1 :: Eq k => k -> v -> Assoc k v -> Proof
-- BY 3 CASES IN insert
prop1 key val []
    =   hasKey key (insert key val []) -- Restate conclusion
    === hasKey key ((key,val):[])      -- Expand `insert`
--  === (key == key || hasKey key [])  -- Expand `hasKey`
--  === (key == key || False)          -- Expand `hasKey`
--  === key == key                     -- Simplify
    *** QED
prop1 key val ((k,v):xs)
  | key == k
    =   hasKey key (insert key val ((key,v):xs)) -- Restate conclusion
    === hasKey key ((key,val):xs)                -- Expand `insert`
--  === (key == key || hasKey key xs)            -- Expand `hasKey`
--  === (True || hasKey key xs)                  -- Simplify
--  === True                                     -- Simplify
    *** QED
  | otherwise
    =   hasKey key (insert key val ((k,v):xs))         -- Restate conclusion
    === hasKey key ((k,v):insert key val xs)           -- Expand `insert`
--  === (key == k || (hasKey key (insert key val xs))) -- Expand `hasKey`
--  === (False || (hasKey key (insert key val xs)))    -- Simplify
    === (hasKey key (insert key val xs))               -- Simplify
        ? prop1 key val xs                             -- Induction hypothesis
--  === True                                           -- Simplify
    *** QED

-- | Automatically prove that after performing an insert the result has the key.
{-@ ple prop2 @-}
{-@
prop2
    :: key:k -> val:v -> xs:Assoc k v
    -> { _:Proof | hasKey key (insert key val xs) }
@-}
prop2 :: Eq k => k -> v -> Assoc k v -> Proof
-- BY 3 CASES IN insert
prop2 key val []
    = ()
prop2 key val ((k,v):xs)
    | key == k = ()
    | otherwise = prop2 key val xs
