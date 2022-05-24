{-@ LIQUID "--skip-module" @-}
{-# OPTIONS_GHC -ddump-splices #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module LambdaEncodingsTHuse where

import qualified Prelude as P
import Prelude ((.), Eq(..), Show(..), Num(..), Monad(..), Applicative(..), (<$>))
import Test.QuickCheck

data Bool where
    True  :: Bool
    False :: Bool
    deriving (Eq, Show)

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

boolToScott :: Bool -> BoolScott_ z
boolToScott True = trueScott
boolToScott False = falseScott
boolFromScott :: BoolScott_ Bool -> Bool
boolFromScott = \bool -> unBoolScott_ bool True False

instance Arbitrary Bool where
    arbitrary = arbitrary >>= \case
        P.True -> return True
        P.False -> return False
-- |
-- !>>> sample (arbitrary :: Gen Bool)
-- prop> prop_boolRoundtrip b
prop_boolRoundtrip :: Bool -> P.Bool
prop_boolRoundtrip b = b == boolFromScott (boolToScott b)




data Nat where
    Succ :: Nat -> Nat
    Zero :: Nat
    deriving (Eq, Show)

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

natToScott :: Nat -> NatScott_ z
natToScott Zero = zeroScott
natToScott (Succ n) = succScott (natToScott n)
natFromScott :: NatScott_ Nat -> Nat
natFromScott = \nat -> unNatScott_ nat (Succ . natFromScott) Zero -- use Haskell's recursion

instance Arbitrary Nat where
    arbitrary = (arbitrary :: Gen P.Word) >>= return . go
      where
        go 0 = Zero
        go n = Succ (go (n - 1))
-- |
-- !>>> sample (arbitrary :: Gen Nat)
-- prop> prop_natRoundtrip n
prop_natRoundtrip :: Nat -> P.Bool
prop_natRoundtrip n = n == natFromScott (natToScott n)




data List a
    = Cons a (List a)
    | Nil
    deriving (Eq, Show)

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

listToScott :: List a -> ListScott_ a z
listToScott Nil = nilScott
listToScott (Cons hd tl) = consScott hd (listToScott tl)
listFromScott :: ListScott_ a (List a) -> List a
listFromScott = \list -> unListScott_ list (\hd tl -> Cons hd (listFromScott tl)) Nil -- use Haskell's recursion

instance Arbitrary a => Arbitrary (List a) where
    arbitrary = arbitrary >>= return . go
      where
        go [] = Nil
        go (x:xs) = Cons x (go xs)
-- |
-- !>>> sample (arbitrary :: Gen (List P.Char))
-- prop> prop_listRoundtrip xs
prop_listRoundtrip :: Eq a => List a -> P.Bool
prop_listRoundtrip xs = xs == listFromScott (listToScott xs)




data Pair a b where
    Pair :: { fst :: a, snd :: b } -> Pair a b
    deriving (Eq, Show)

newtype PairScott_ a b z = PairScott_
    { unPairScott_
        :: (a -> b -> z)    -- pair
        -> z
    }
pairScott :: a -> b -> PairScott_ a b z
pairScott = \fst_ snd_ -> PairScott_ (\pair -> pair fst_ snd_)

pairToScott :: Pair a b -> PairScott_ a b z
pairToScott (Pair fst_ snd_) = pairScott fst_ snd_
pairFromScott :: PairScott_ a b (Pair a b) -> Pair a b
pairFromScott = \pair -> unPairScott_ pair Pair

instance (Arbitrary a, Arbitrary b) => Arbitrary (Pair a b) where
    arbitrary = Pair <$> arbitrary <*> arbitrary
-- |
-- !>>> sample (arbitrary :: Gen (Pair P.Int P.Char))
-- prop> prop_pairRoundtrip xs
prop_pairRoundtrip :: (Eq a, Eq b) => Pair a b -> P.Bool
prop_pairRoundtrip p = p == pairFromScott (pairToScott p)




data These a b where
    A    :: a      -> These a b
    B    ::      b -> These a b
    Both :: a -> b -> These a b
    deriving (Eq, Show)

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

theseToScott :: These a b -> TheseScott_ a b z
theseToScott (A a) = aScott a
theseToScott (B b) = bScott b
theseToScott (Both a b) = bothScott a b
theseFromScott :: TheseScott_ a b (These a b) -> These a b
theseFromScott = \these -> unTheseScott_ these A B Both

instance (Arbitrary a, Arbitrary b) => Arbitrary (These a b) where
    arbitrary = oneof
        [ A <$> arbitrary
        , B <$> arbitrary
        , Both <$> arbitrary <*> arbitrary
        ]
-- |
-- !>>> sample (arbitrary :: Gen (These P.Int P.Char))
-- prop> prop_theseRoundtrip xs
prop_theseRoundtrip :: (Eq a, Eq b) => These a b -> P.Bool
prop_theseRoundtrip t = t == theseFromScott (theseToScott t)
