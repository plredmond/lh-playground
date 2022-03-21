{-# LANGUAGE GADTs #-}

module UniqueList where

{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data" @-}




-- * Part I

-- | Function to determine whether a value is present in a list.
listElem :: Eq a => a -> [a] -> Bool
listElem _ [] = False
listElem e (x:xs) = e==x || listElem e xs
{-@ reflect listElem @-}

-- | Type of a list containing only distinct elements.
{-@ type UList a = [a]<{\x y -> x /= y}> @-}

-- | Function to make the preconditions of adding to a UList explicit.
{-@ uCons :: e:a -> UList ({x:a | e /= x}) -> UList a @-}
uCons :: a -> [a] -> [a]
uCons e xs = e : xs
{-@ reflect uCons @-}

-- | Convert evidence about list membership.
{-@
convert
    :: e:a
    -> {xs:UList a | not (listElem e xs)}
    -> {ys:UList ({y:a | e /= y}) | xs == ys}
@-}
---- {-@
---- convert
----     :: forall <proc :: a -> a -> Bool>.
----        e:a
----     -> {xs:[a]<proc> | not (listElem e xs)}
----     -> {ys:[{y:a | e /= y}]<proc> | xs == ys}
---- @-}
convert :: Eq a => a -> [a] -> [a]
convert _e [] = []
convert e (x:xs) = x : convert e xs
{-@ ple convert @-}
{-@ reflect convert @-}

{-@ nelCons :: e:a -> {xs:UList a | not (listElem e xs)} -> UList a @-}
nelCons :: Eq a => a -> [a] -> [a]
--nelCons e xs = uCons e (xs `withProof` convert e xs)
--nelCons e xs = uCons (e `withProof` convert e xs) xs
--nelCons e xs = (uCons `withProof` convert e xs) e xs
--nelCons e xs = uCons e (convert e xs === xs)
nelCons e xs = uCons e (convert e xs)
{-@ ple nelCons @-}
{-@ reflect nelCons @-}




-- * Part II

-- | Add an extra argument to cons, and apply the abstract refinement to head
-- and tail.
data L a where
    C :: a -> L a -> () -> L a
    N :: L a
{-@
data L a <p :: a -> L a -> () -> Bool> where
    C :: x:a -> xs:L<p> a -> ()<p x xs> -> L<p> a
    N :: L<p> a
@-}

lElem :: Eq a => a -> L a -> Bool
lElem _ N = False
lElem e (C x xs ()) = e==x || lElem e xs
{-@ reflect lElem @-}

{-@ type UL a = L<{\x xs _ -> not (lElem x xs)}> a @-}

-- | Get constant time cons back.
{-@ cons :: x:a -> {xs:UL a | not (lElem x xs)} -> UL a @-}
cons :: a -> L a -> L a
cons x xs = C x xs ()
