{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Henzinger60_Refinements where

-- Extracted from Ranjit Jhala's henzinger60 paper

import Language.Haskell.Liquid.ProofCombinators ()

-- Representation of a graph E as a subset of (V x V).
type Edge v = v -> v -> Bool

-- Reads as "X reaches Y following edges E"
data ReachProp v where
  ReachProp :: Edge v -> v -> v -> ReachProp a

-- Judgements-as-types encoding of
--
--  [Self] -----------
--          x -->*e x
--
--          (x,y) ∈ e   y -->*e z
--  [Step] -----------------------
--                x -->*e z
data ReachEv a where
      Self :: Edge a -> a ->
              ReachEv a
      Step :: Edge a -> a -> a -> a ->
              ReachEv a ->
              ReachEv a
{-@ data ReachEv a where
      Self :: e:Edge a -> x:a -> 
              Prop {ReachProp e x x}
      Step :: e:Edge a -> x:a -> y:{a|e x y} -> z:a -> 
              Prop {ReachProp e y z} -> 
              Prop {ReachProp e x z}
@-}

--- {-@ reachTrans :: e:Edge a -> x:a -> y:a -> z:a -> 
---               Prop {ReachProp e x y} -> Prop {ReachProp e y z} ->
---               Prop {ReachProp e x z} @-}
--- reachTrans :: Edge a -> a -> a -> a -> ReachEv a -> ReachEv a -> ReachEv a
--- reachTrans e x y z pXY pYZ =
---     case pXY of
---         Self _e _x -> {- Self means x=y. -} undefined-- FIXME pYZ
---         Step _e _x _yXY _z _pYZ -> undefined
--- 
--- -- reachTrans e x y z (Self _ _) yz          = yz
--- -- reachTrans e x y z (Step _ _ x1 _ x1y) yz = Step e x x1 z x1z 
--- --   where x1z = reachTrans e x1 y z x1y yz

