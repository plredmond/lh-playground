module UniqueList where

-- import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data" @-}

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
convert e (x:xs) | e /= x = x : convert e xs
{-@ ple convert @-} -- So that LH knows there's only the @e /= x@ case.

{-@ nelCons :: e:a -> {xs:UList a | not (listElem e xs)} -> UList a @-}
nelCons :: Eq a => a -> [a] -> [a]
--nelCons e xs = uCons e (xs `withProof` convert e xs)
--nelCons e xs = uCons (e `withProof` convert e xs) xs
--nelCons e xs = (uCons `withProof` convert e xs) e xs
--nelCons e xs = uCons e (convert e xs === xs)
nelCons e xs = uCons e (convert e xs)
{-@ ple nelCons @-}
