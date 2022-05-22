{-@ LIQUID "--skip-module" @-}
{-# OPTIONS_GHC -ddump-splices #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
module LambdaEncodingsTHuse where


data Bool where
    True  :: Bool
    False :: Bool

newtype BoolScott_ z = BoolScott_
    { unBoolScott_
        :: z    -- true
        -> z    -- false
        -> z
    }
trueScott :: BoolScott_ z
trueScott = BoolScott_ (\true _false -> true)
falseScott :: BoolScott_ z
falseScott = BoolScott_ (\_true false -> false)

data Nat where
    Succ :: Nat -> Nat
    Zero :: Nat

newtype NatScott_ z = NatScott_
    { unNatScott_
        :: (NatScott_ z -> z)   -- succ
        -> z                    -- zero
        -> z
    }
succScott :: NatScott_ z -> NatScott_ z
succScott = \nat -> NatScott_ (\succ _zero -> succ nat)
zeroScott :: NatScott_ z
zeroScott = NatScott_ (\_succ zero -> zero)

data List a
    = Cons a (List a)
    | Nil

newtype ListScott_ a z = ListScott_
    { unListScott_
        :: (a -> ListScott_ a z -> z)   -- cons
        -> z                            -- nil
        -> z
    }
consScott :: a -> ListScott_ a z -> ListScott_ a z
consScott = \head tail -> ListScott_ (\cons _nil -> cons head tail)
nilScott :: ListScott_ a z
nilScott = ListScott_ (\_cons nil -> nil)

data Pair a b where
    Pair :: { fst :: a, snd :: b } -> Pair a b

newtype PairScott_ a b z = PairScott_
    { unPairScott_
        :: (a -> b -> z)    -- pair
        -> z
    }
pairScott :: a -> b -> PairScott_ a b z
pairScott = \fst_ snd_ -> PairScott_ (\pair -> pair fst_ snd_)

data These a b where
    A    :: a      -> These a b
    B    ::      b -> These a b
    Both :: a -> b -> These a b

newtype TheseScott_ a b z = TheseScott_
    { unTheseScott_
        :: (a      -> z)
        -> (     b -> z)
        -> (a -> b -> z)
        -> z
    }
aScott :: a -> TheseScott_ a b z
aScott = \fst_ -> TheseScott_ (\a _b _both -> a fst_)
bScott :: b -> TheseScott_ a b z
bScott = \snd_ -> TheseScott_ (\_a b _both -> b snd_)
bothScott :: a -> b -> TheseScott_ a b z
bothScott = \fst_ snd_ -> TheseScott_ (\_a _b both -> both fst_ snd_)
