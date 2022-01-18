{-@ LIQUID "--reflection" @-}
--- LIQUID "--exact-data-cons" @-}
--- LIQUID "--exact-data" @-}
--- LIQUID "--no-adt" @-}
{-@ LIQUID "--ple-local" @-}
module TransitionSystemLarge where

import Language.Haskell.Liquid.ProofCombinators

listFoldr :: (a -> b -> b) -> b -> [a] -> b
listFoldr f acc (x:xs) = f x (listFoldr f acc xs)
listFoldr _ acc [] = acc
{-@ reflect listFoldr @-}

-------------------------------------------------------------------------------
-- Model the nats with ints

data State
    = State Integer

state0 :: State
state0 = State 0
{-@ reflect state0 @-}

-- | Inference rules
data Rule
    = Add Integer
    | Sub Integer
    deriving Eq

-- | Premises for each possible rule application
premisesHold :: State -> Rule -> Bool
premisesHold (State _) (Add n) = 0 <= n -- n is a nat
premisesHold (State m) (Sub n) = 0 <= n -- n is a nat
                              && n <= m -- (m - n) is a nat
{-@ reflect premisesHold @-}

-- | Transition function for valid rule applications
{-@ transition :: s:State -> {r:Rule | premisesHold s r} -> State @-}
transition :: State -> Rule -> State
transition (State m) (Add n) = State (m + n)
transition (State m) (Sub n) = State (m - n)
{-@ reflect transition @-}

-- | Apply a sequence of rules to obtain a final state, unless the
-- premises do not hold for some intermediate state
applyRules :: [Rule] -> Maybe State
applyRules rules = listFoldr applyRulesHelper (Just state0) rules
{-@ reflect applyRules @-}
applyRulesHelper :: Rule -> Maybe State -> Maybe State
applyRulesHelper _ Nothing = Nothing
applyRulesHelper rule (Just state)
    | premisesHold state rule = Just (transition state rule)
    | otherwise = Nothing
{-@ reflect applyRulesHelper @-}

-- | Valid sequence of inference rule applications
{-@ type ValidRules = {rules:[Rule] | isJust (applyRules rules)} @-}

-- | Reachable state
{-@ applyValidRules :: ValidRules -> State @-}
applyValidRules :: [Rule] -> State
applyValidRules rules = case applyRules rules of Just state -> state
{-@ reflect applyValidRules @-}

{-@ tailValidRulesIsValid :: {rules:ValidRules | rules /= []} -> { isJust (applyRules (tail rules)) } @-}
tailValidRulesIsValid :: [Rule] -> Proof
tailValidRulesIsValid (_r:rs) = case applyRules rs of
    Just _ -> () *** QED
    Nothing -> () *** QED
--  Nothing
--      ->  applyRules (r:rs) -- premise ValidRules means this is a Just
--      === applyRulesHelper r (applyRules rs)
--      === applyRulesHelper r Nothing -- by case split this is a Nothing
--      === Nothing
--      *** QED
{-@ ple tailValidRulesIsValid @-}

{-@ tailValidRulesPremisesHold :: {rules:ValidRules | rules /= []} -> { premisesHold (applyValidRules (tail rules)) (head rules) } @-}
tailValidRulesPremisesHold :: [Rule] -> Proof
tailValidRulesPremisesHold (r:rs) = () *** Admit
--  =
--  let rs' = rs ? tailValidRulesIsValid (r:rs)
--  in  premisesHold (applyValidRules rs') r
--  *** Admit
--  =   applyRules (r:rs) -- premise ValidRules means this is a Just
--  === applyRulesHelper (head (r:rs)) (applyRules (tail (r:rs)))
--  === applyRulesHelper r (applyRules rs)
--  *** Admit
{-@ ple tailValidRulesPremisesHold @-}

-------------------------------------------------------------------------------
-- Prove a property about reachable nats

-- | Nats are positive
napProp :: State -> Bool
napProp (State m) = 0 <= m
{-@ reflect napProp @-}

{-@ preservation :: {s:State | napProp s} -> {r:Rule | premisesHold s r} -> { napProp (transition s r) } @-}
preservation :: State -> Rule -> Proof
preservation _ _ = () -- Follows from the definitions
{-@ ple preservation @-}

---- preservation (State m) (Add n)
----     =   napProp (State m)
---- --  === 0 <= m
----     === premisesHold (State m) (Add n)
---- --  === 0 <= n
----     === napProp (transition (State m) (Add n))
---- --  === napProp (State (m + n))
---- --  === 0 <= (m + n)
----     *** QED
---- preservation (State m) (Sub n)
----     =   () *** Admit

-- | Reachable nats are positive
{-@ anapProp :: ValidRules -> Bool @-}
anapProp :: [Rule] -> Bool
anapProp rules = napProp (applyValidRules rules)
{-@ reflect anapProp @-}

--{-@ anapProof :: rules:ValidRules -> { anapProp rules } @-}
--anapProof :: [Rule] -> Proof
--anapProof [] = ()
--anapProof (r:rs)
--    =   applyRules (r:rs)
--    === applyRulesHelper r (applyRules rs)
--        ? tailValidRulesIsValid (r:rs)
--        ? anapProof rs
--        ? tailValidRulesPremisesHold (r:rs)
--        ? preservation (applyValidRules rs) r
--    *** QED
--{-@ ple anapProof @-}
