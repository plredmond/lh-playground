{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
module GhostState where

--          {p} C {q}
-- [frame]-------------
--        {p*r} C {q*r}

import Language.Haskell.Liquid.ProofCombinators

-- IMPORTED: measure prop :: a -> b
-- IMPORTED: type Prop E = {v:_ | prop v = E}

-- data HistoryProp
--     = Add Int Int
--     | Sub Int Int
-- 
-- -- {-@ add :: a:_ -> b:_ -> Prop {Add a b} @-}
-- -- add :: Int -> Int -> Int
-- -- add a b = a + b
-- 
