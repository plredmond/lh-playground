{-@ LIQUID "--reflection" @-}

-- | https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
module Sf2PlfHoarePtI where

-- {-@ type Assertion A = {s:_ | A s} @-}
-- 
-- {-@ type Triple  P Q = {s:_ | P s} -> {s':_ | Q s} @-}
-- {-@ type Triple' P Q = Assertion {P} -> Assertion {Q} @-}
-- 
-- type Var = String
-- type Val = Int
-- type State = Var -> Val
-- 
-- -- type Item k v = (k, v)
-- -- type Assoc k v = [Item k v]
-- -- type State = Assoc Var Val
-- -- 
-- -- get :: Var -> State -> Maybe Val
-- -- get _tgt [] = Nothing
-- -- get  tgt ((var,val):rest)
-- --     | tgt == var = Just val
-- --     | otherwise = get tgt rest
-- -- {-@ reflect get @-}
-- 
-- (===) :: Var -> Val -> State -> Bool
-- (var === val) st = st var == val
-- {-@ reflect === @-}
-- 
-- impAssign :: 
-- (:=) = ()
