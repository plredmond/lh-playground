{-@ LIQUID "--reflection" @-}

module ICantBelieveItCanSort where

import Prelude hiding (foldl)

-- $setup
-- >>> import Data.List

-- for i=1 to n do
--  for j=1 to n do
--   if A[i] < A[j] then
--    swap A[i] and A[j]
--
-- https://twitter.com/kmett/status/1523114705836904449

{-@ type Index XS = Fin {len XS} @-}
{-@ type Size XS = {n:Nat | n == len XS} @-}

-- | Loop body gets an array and and index into it and returns the array.
type LoopBody a = [a] -> Int -> [a]
{-@ type LoopBody a N = {bs:[a] | len bs == N} -> Fin {N} -> {ds:[a] | len ds == N} @-}

{-@ forHelper :: xs:[a] -> i:Index {xs} -> n:Size {xs} -> LoopBody a {n} -> {ys:[a] | len xs == len ys} / [n - i] @-}
forHelper :: [a] -> Int -> Int -> LoopBody a -> [a]
forHelper xs i n body
    | i+1 < n   = forHelper (body xs i) (i+1) n body
    | otherwise =            body xs i
{-@ reflect forHelper @-}

{-@ for :: xs:[a] -> LoopBody a {len xs} -> {ys:[a] | len xs == len ys} @-}
for :: [a] -> LoopBody a -> [a]
for [] _body = []
for xs  body = forHelper xs 0 (listLength xs) body
{-@ reflect for @-}

-- | Illustrate how we implement it.
-- prop> sort xs == icbicsFor xs
icbicsFor :: Ord a => [a] -> [a]
icbicsFor xs =
    for xs $ \ys i ->
        for ys $ \zs j ->
            if listIndex zs i < listIndex zs j
            then listSwap zs i j
            else zs

-- |
-- prop> sort xs == icbics xs
icbics :: Ord a => [a] -> [a]
icbics xs =
    for xs (icbicsBody1 $ listLength xs)
{-@ reflect icbics @-}

{-@ icbicsBody1 :: n:Nat -> LoopBody a {n} @-}
icbicsBody1 :: Ord a => Int -> LoopBody a
icbicsBody1 n ys i =
    for ys (icbicsBody2 n i)
{-@ reflect icbicsBody1 @-}

{-@ icbicsBody2 :: n:Nat -> Fin {n} -> LoopBody a {n} @-}
icbicsBody2 :: Ord a => Int -> Int -> LoopBody a
icbicsBody2 _n i zs j =
    if listIndex zs i < listIndex zs j
    then listSwap zs i j
    else zs
{-@ reflect icbicsBody2 @-}




foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _f b []     = b
foldl  f b (a:as) = foldl f (f b a) as
{-@ reflect foldl @-}

{-@ ignore icbicsFold @-} -- LH cannot tell that the indexes are in range
-- |
-- prop> sort xs == icbicsFold xs
icbicsFold :: Ord a => [a] -> [a]
icbicsFold xs =
    let n = listLength xs
        indexes = finAsc n
    in
        foldl (\ys i ->
            foldl (\zs j ->
                if listIndex zs i < listIndex zs j
                then listSwap zs i j
                else zs)
            ys indexes)
        xs indexes




-- * Array (modeled with list)

{-@ listIndex :: xs:[a] -> Index {xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i = if i==0 then x else listIndex xs (i-1)
{-@ reflect listIndex @-}

{-@ listUpdate :: xs:[a] -> Index {xs} -> x:a -> {ys:[a] | len xs == len ys} @-}
listUpdate :: [a] -> Int -> a -> [a]
listUpdate (x:xs) i x' = if i==0 then x':xs else x:listUpdate xs (i-1) x'
{-@ reflect listUpdate @-}

{-@ listSwap :: xs:[a] -> Index {xs} -> Index {xs} -> {ys:[a] | len xs == len ys} @-}
listSwap :: [a] -> Int -> Int -> [a]
listSwap xs i j =
    let xs_i = xs `listIndex` i
        xs_j = xs `listIndex` j
    in listUpdate (listUpdate xs i xs_j) j xs_i
{-@ reflect listSwap @-}

{-@ listLength :: xs:[a] -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}





-- * Finite set

-- | A member of a finite set of natural numbers. (Agda's Fin)
{-@ type Fin V = {k:Nat | k < V} @-}

-- | A whole finite set in descending/ascending order as a list.
{-@ type FinDesc N = {xs:[Fin {N}]<{\a b -> a > b}> | len xs == N} @-}
{-@ type FinAsc  N = {xs:[Fin {N}]<{\a b -> a < b}> | len xs == N} @-}

-- | Generate the elements of a finite set @Fin n@ in ascending order
--
-- >>> finAsc (-1)
-- []
-- >>> finAsc 0
-- []
-- >>> finAsc 1
-- [0]
-- >>> finAsc 2
-- [0,1]
-- >>> finAsc 3
-- [0,1,2]
--
{-@ finAsc :: n:Nat -> FinAsc {n} @-}
finAsc :: Int -> [Int]
finAsc n = finAscHelper 0 n
{-@ reflect finAsc @-}

-- | Returns bounded by [m..n) in ascending order.
--
-- >>> finAscHelper 4 9
-- [4,5,6,7,8]
--
{-@
finAscHelper
    ::  m:Nat
    -> {n:Nat | m <= n}
    -> {xs:[{x:Nat | m <= x && x < n}]<{\a b -> a < b}> | len xs == n-m}
    / [n-m]
@-}
finAscHelper :: Int -> Int -> [Int]
finAscHelper m n =
    if m < n
    then m : finAscHelper (m+1) n
    else []
{-@ reflect finAscHelper @-}
