---
title: Abstract refinements
...

<!--
Build this document with the following:

pandoc lib/AbsRef.lhs --from=markdown+lhs --to=html --standalone --toc
-->

What's an abstract refinement?
------------------------------

How do you talk about sorted data structures or structures containing unique
elements in Liquid Haskell? One way is to define a data structure for each
purpose, with hard-coded refinements to describe the relationships between its
fields. Another way is to define the data structure once with an abstract
refinement.^[This document is a very short and very incomplete introduction to
abstract refinements. There's way more information in [these
slides](https://github.com/ucsd-progsys/liquidhaskell/blob/07c28f992eebe07e7a782c17fb1ac597e37ddb5c/docs/slides/niki/lhs/AbstractRefinements.lhs).]
Then when you have a need for additional constraints, you provide a function to
express the relationship you want.

An abstract refinement is a refinement with some details left out. You can fill
in those details later by providing a function. The abstract refinement says
how to apply the function to values and types to obtain a concrete refinement,
and they can be added to both data definitions and to function types.

The most common abstract refinement is the built-in one that's defined on list
`[]`{.haskell}, but because it's built-in, the definition isn't available.
Let's clear up the mystery around that. First we'll talk about how to use it,
then how to define it.

> {-# LANGUAGE GADTs #-}
> module AbsRef where

Use on a data structure
-----------------------

Here is an example of *using* the built-in abstract refinement defined on lists
`[]`{.haskell}, to declare a type alias for lists sorted in ascending order.

> {-@ type Ascending a = [a]<{\x y -> x < y}> @-}

`Ascending`{.haskell} is an alias for a normal list `[a]`{.haskell} refined
with the function `\x y -> x < y`{.haskell}. When this function is applied to
the built-in abstract refinement on the list type, each cons cell
`x:ys`{.haskell} throughout the list is constrained such that `x`{.haskell} is
less than every element `y`{.haskell} in its adjacent tail `ys`{.haskell}. This
comes from the use of our function to express a constraint on the fields of the
`:`{.haskell} constructor which you could imagine like this:

```.haskell
(:) :: x:a -> [{y:a | x < y}] -> [a]
```

It's not clear where this constraint comes from, because we can't see how the
abstract refinement is defined! Let's look briefly at a couple examples which
use `Ascending`{.haskell} to understand it concretely, and then we'll look at
how to define the abstract refinement relating heads to tails.

> {-@ eg1 :: Ascending Char @-}
> eg1 :: String
> eg1 = 'a':'b':'c':[]

Concretely, the inequalities `'a' < 'b'`{.haskell}, `'a' < 'c'`{.haskell}, and
`'b' < 'c'`{.haskell} are verified at compile time.

> {-@ eg2 :: Ascending Char @-}
> eg2 :: String
> eg2 = 'a':'c':'b':[]
> {-@ fail eg2 @-}

Since `'c' ≮ 'b'`{.haskell}, the binder `eg2`{.haskell} results in a compile
error.

We can directly state the evidence given by an abstract refinement with a
function to extract the tail of a non-empty `Ascending`{.haskell} and constrain
it: `head xs`{.haskell} is less than each element `x`{.haskell} in the tail of
`xs`{.haskell}.

> {-@ meaning
>         :: {xs:Ascending a | xs /= []}
>         -> [{x:a | head xs < x}] @-}
> meaning :: [a] -> [a]
> meaning (_:tl) = tl

The syntax `[a]<{\x y -> x < y}>`{.haskell} makes a little more sense to me
when I think of it as relating the head to each element of the tail as in the
above type.

Definition on a data structure
------------------------------

It's all well and good to use predefined and built-in abstract refinements, but
let's look at how to *define* them yourself. Here is a list defined in normal
ADT syntax with an abstract refinement `p`{.haskell} that relates each element
to all elements in tail.^[Naming and syntax from [this
slide](https://github.com/ucsd-progsys/liquidhaskell/blob/07c28f992eebe07e7a782c17fb1ac597e37ddb5c/docs/slides/niki/lhs/AbstractRefinements.lhs#L180-L187).]
The built-in abstract refinement on `[]`{.haskell} is probably defined
similarly.

> data L a
>     = C a (L a)
>     | N
> {-@
> data L a <p :: a -> a -> Bool>
>     = C
>         (h :: a)
>         (t :: L<p> a<p h>)
>     | N
> @-}

Elements of note:

1. `<p :: a -> a -> Bool>`{.haskell} is declared *after* type variables on the
head of the declaration.

1. `L<p>`{.haskell} applies `p`{.haskell} to `L`{.haskell} *before* the type
variables in the recursive part of the definition. This ensures that the
abstract refinement is threaded through every part of the nested structure.

1. `a<p h>`{.haskell} applies `p`{.haskell} to the head value, `h`{.haskell},
and the type of elements in the tail, `a`{.haskell}, to establish the evidence
which is available when pattern matching.

All the while, `p`{.haskell} is left abstract! You can provide a function later
to say what evidence is available when using the data structure.

Here's that same definition, written out in GADT syntax.^[Using GADT syntax has
the advantage of not defining measures for the fields of the type. I think the
ADT definition made measures (`h :: L a -> a`{.haskell} and `t :: L a -> L
a`{.haskell}) which pollute the Liquid Haskell namespace.] The type and
constructors have "G" appended to differentiate from the previous definition.

> data LG a where
>     CG :: a -> LG a -> LG a
>     NG :: LG a
> {-@
> data LG a <p :: a -> a -> Bool> where
>     CG
>         :: h : a
>         -> t : LG<p> a<p h>
>         ->     LG<p> a
>     NG
>         ::     LG<p> a
> @-}

This definition must state the refinements on the resulting type explicitly, as
you do with GADTs.^[I don't know which of these are required. Some seem
optional because the functions defined later typecheck without them.]

Definition on a function
------------------------

This is the syntax to define an abstract refinement on a function type.

> {-@ lFromList :: forall <p :: a -> a -> Bool>. [a]<p> -> L<p> a @-}
> lFromList :: [a] -> L a
> lFromList [] = N
> lFromList (x:xs) = C x (lFromList xs)

The function `lFromList`{.haskell} constructs an `L<p> a`{.haskell} from a
given `[a]<p>`{.haskell}, allowing you to convert an `Ascending a`{.haskell}
(which is `[a]<{\x y -> x < y}>`{.haskell}) to a `L<{\x y -> x < y}>
a`{.haskell}. The function isn't terribly interesting, but serves to document
the syntax which includes:

1. `forall <p :: a -> a -> Bool>.`{.haskell} declares the abstract refinement
for use in the signature.

1. `[a]<p>`{.haskell} and `L<p> a`{.haskell} show application of `p`{.haskell}
to types with abstract refinements.

Here are two more conversions to complete the triangle.

> {-@ lgFromL :: forall <p :: a -> a -> Bool>. L<p> a -> LG<p> a @-}
> lgFromL :: L a -> LG a
> lgFromL N = NG
> lgFromL (C x xs) = CG x (lgFromL xs)
>
> {-@ listFromLG :: forall <p :: a -> a -> Bool>. LG<p> a -> [a]<p> @-}
> listFromLG :: LG a -> [a]
> listFromLG NG = []
> listFromLG (CG x xs) = x : listFromLG xs

Last, here's an example showing that we can pass an `Ascending`{.haskell}
through several transformations, and still know that we have an ascending list
at the end.

> {-@ roundtrip :: Ascending a -> Ascending a @-}
> roundtrip :: [a] -> [a]
> roundtrip xs = listFromLG (lgFromL (lFromList xs))

Why do we want abstract refinements?
---------------------------------------

You can get pretty far without abstract refinements by defining bespoke data
structures with hardcoded relationships between elements. Here's a descending
list.

> data Descending a
>     = DescCons a (Descending a)
>     | DescNil
> {-@
> data Descending a
>     = DescCons
>         (dh :: a)
>         (dt :: Descending {v:a | dh > v })
>     | DescNil
> @-}

This is the same amount of work as it was to define `L a`{.haskell} above, but
there's no flexibility. `Descending`{.haskell} can only be used to represent
descending lists and won't work with existing list functions without explicit
$O(n)$ conversions.

Other reasons you might want to use abstract refinements:

* You have a monomorphic structure, but you want it to be "polymorphic" in the
  constraints it imposes.

* You want to relate multiple fields, but not the same way every time.

* You want invariants between arguments to be preserved, without knowing what
  those invariants are.

Let's start with dependent pairs. Without abstract refinements, you can define
them bespoke to their purpose.

> data PairDoubled where
>     PairDoubled :: Int -> Int -> PairDoubled
> {-@
> data PairDoubled where
>     PairDoubled :: x:_ -> {y:_ | 2 * x == y} -> PairDoubled
> @-}
>
> eg3 :: PairDoubled
> eg3 = PairDoubled 4 8
>
> eg4 :: PairDoubled
> eg4 = PairDoubled 0 8
> {-@ fail eg4 @-}

`PairDoubled`{.haskell} is a monomorphic data structure which can only contains
pairs of `Int`{.haskell} where the second is twice the first. What if you want
it to be three times?

> data PairHead a where
>     PairHead :: a -> [a] -> PairHead a
> {-@
> data PairHead a where
>     PairHead :: x:a -> {y:[a] | x == head y} -> PairHead a
> @-}
>
> eg5 :: PairHead Char
> eg5 = PairHead 'H' ('H':"ello")
>
> eg6 :: PairHead Int
> eg6 = PairHead 3 [2,1]
> {-@ fail eg6 @-}

`PairHead`{.haskell} is a data structure which can only contain pairs of
`a`{.haskell} and `[a]`{.haskell} where the first is the head element of the
second.

Instead of defining a new datatype for every use case, you can define a general
dependent pair.

> data Pair a b where
>     Pair :: a -> b -> Pair a b
> {-@
> data Pair a b <p :: a -> b -> Bool> where
>     Pair :: x:a -> y:b<p x> -> Pair<p> a b<p y>
> @-}

`Pair`{.haskell} is a data structure with an abstract refinement which
constrains the second element of the pair with a predicate on the first. Let's
reimplement `PairDoubled`{.haskell} and `PairHead`{.haskell}.

> {-@ type PairNTimes N = Pair<{\x y -> N * x == y}> Int Int @-}
>
> {-@ eg3' :: PairNTimes {2} @-}
> eg3' :: Pair Int Int
> eg3' = Pair 4 8
>
> {-@ eg4' :: PairNTimes {2} @-}
> eg4' :: Pair Int Int
> eg4' = Pair 0 8
> {-@ fail eg4' @-}

You can constrain `PairNTimes`{.haskell} with different values known at
runtime.

> {-@ dependent :: x:Int -> y:Int -> PairNTimes {y} @-}
> dependent :: Int -> Int -> Pair Int Int
> dependent x y = Pair x (x * y)

Here's `PairHead`{.haskell} redefined.

> {-@ type PairHead' a = Pair<{\x y -> x == head y}> a [a] @-}
> {-@ eg5' :: PairHead' Char @-}
> eg5' :: Pair Char String
> eg5' = Pair 'H' ('H':"ello")
>
> {-@ eg6' :: PairHead' Int @-}
> eg6' :: Pair Int [Int]
> eg6' = Pair 3 [2,1]
> {-@ fail eg6' @-}

The general dependent pair is already in Liquid Haskell, too.

> {-@ type AscPair a b = (a, b)<{\x y -> x < y}> @-}
>
> {-@ eg7 :: AscPair Int Int @-}
> eg7 :: (Int, Int)
> eg7 = (3, 12)
>
> {-@ eg8 :: AscPair Int Int @-}
> eg8 :: (Int, Int)
> eg8 = (120, 12)
> {-@ fail eg8 @-}

Have Fun! The sourcecode for this document is:
<https://github.com/plredmond/lh-playground/blob/main/lib/AbsRef.lhs>.
