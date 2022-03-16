---
title: Abstract refinements
...

What's an abstract refinement?
------------------------------

How do you talk about sorted structures or structures containing unique
elements in Liquid Haskell?  Use abstract refinements. ^[This document is a
very short and very incomplete introduction to abstract refinements. There's
way more information in [these
slides](https://github.com/ucsd-progsys/liquidhaskell/blob/07c28f992eebe07e7a782c17fb1ac597e37ddb5c/docs/slides/niki/lhs/AbstractRefinements.lhs).]

An abstract refinement is a higher-order function argument in a refinement.
Abstract refinements let you write refinements which can be made concrete
later by applying a function.

The most common abstract refinement is the built-in one that's defined on list
`[]`{.haskell}, but because it's built in there's still mystery about abstract
refinements. Let's go over that.

> {-# LANGUAGE GADTs #-}
> module AbsRef where

Use on a data structure
-----------------------

Here is how you might define the type of lists sorted in ascending order, by
using the abstract refinement defined on lists.

> {-@ type Ascending a = [a]<{\x y -> x < y}> @-}

`Ascending`{.haskell} is a normal list `[a]`{.haskell} refined with the
function `\x y -> x < y`{.haskell}. Combined with the abstract refinement
built-in to the list type, this means that each head `x`{.haskell} is less than
every element `y`{.haskell} in its adjacent tail. Let's look at an example.

> {-@ eg1 :: Ascending Char @-}
> eg1 :: String
> eg1 = 'a':'b':'c':[]

Concretely, the inequalities `'a' < 'b'`{.haskell}, `'a' < 'c'`{.haskell}, and
`'b' < 'c'`{.haskell} are verified at compile time.

> {-@ eg2 :: Ascending Char @-}
> eg2 :: String
> eg2 = 'a':'c':'b':[]

Since `'c' ≮ 'b'`{.haskell}, the binder `eg2`{.haskell} is a compile error.

> {-@ fail eg2 @-}

We can directly state the evidence given by an abstract refinement with a
function to extract the tail of a non-empty `Ascending`{.haskell} and
constrain it: Each element `x`{.haskell} in the tail of `xs`{.haskell} is less
than `head xs`{.haskell}.

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

It's all well and good to work with predefined and built-in abstract
refinements, but let's look at how to define them yourself. Here is a list
defined in normal ADT syntax with an abstract refinement `p`{.haskell} that
relates each element to all elements in tail.

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
>         ->     LG<p> a<p h>
>     NG
>         ::     LG<p> a
> @-}

We now state the refinements on the resulting type explicitly, as you do with
GADTs.^[I don't know which of these are required. Some seem optional because
the functions defined later typecheck without them.]

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

Why do we want to abstract refinements?
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
there's no flexibility. `Decending`{.haskell} can only be used to represent
descending lists and won't work with existing list functions without explicit
$O(n)$ conversions.

Have Fun!^[The sourcecode for this document is:
<https://github.com/plredmond/lh-playground/blob/main/lib/AbsRef.lhs>]
