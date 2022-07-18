module RefinedDomains where 

{-@ LIQUID "--ple" @-}

import Relation.Equality.Prop 
-- import Language.Haskell.Liquid.ProofCombinators
import Data.Refined.Unit

--------------------------------------------------------------------------------
-- | Main theorem
--------------------------------------------------------------------------------

pf :: EqualityProp (Integer -> Integer)
{-@ pf :: EqualProp (x:{Integer | 0 <= x } -> Integer) {add1Int} {add1Nat} @-}
pf = extensionality add1Int add1Nat (\x -> refl (add1Int x))


pf' :: EqualityProp (Integer -> Integer)
{-@ pf' :: EqualProp (x:{Integer | 0 <= x } -> {x:Integer | 0 <= x }) add1Int add1Nat @-}
pf' = extensionality add1Int add1Nat pf0' 

pf0' :: Integer -> EqualityProp Integer
{-@ pf0' :: x:{Integer | 0 <= x } ->  EqualProp {x:Integer | 0 <= x } (add1Int x) (add1Nat x) @-}
pf0' x = baseEq (add1Int x) (add1Nat x) (reflP (add1Int x))

pf'' :: EqualityProp (Integer -> Integer)
{-@ pf'' :: EqualProp (x:{Integer | 0 <= x } -> {v:Integer | v = x + 1 }) add1Int add1Nat @-}
pf'' = deqFun add1Int add1Nat pf0'' 

pf0'' :: Integer -> EqualityProp Integer
{-@ pf0'' :: x:{Integer | 0 <= x } ->  EqualProp {v:Integer | v = x + 1 } (add1Int x) (add1Nat x) @-}
pf0'' x = baseEq (add1Int x) (add1Nat x) (reflP (add1Int x))


--------------------------------------------------------------------------------
-- | Bad proofs that should fail
--------------------------------------------------------------------------------
{- 
pfBadRange :: () ->  EqualityProp (Integer -> Integer)
{-@ fail pfBadRange @-}
{-@ pfBadRange :: () -> EqualProp (x:{Integer | 0 <= x } -> {x:Integer | 0 > x }) add1Int add1Nat @-}
pfBadRange _ = eqFun add1Int add1Nat (\x -> extensionality (add1Int x) (add1Nat x) ())

pf0BadRange :: Integer -> EqualityProp Integer
{-@ fail pf0BadRange @-}
{-@ pf0BadRange :: x:{Integer | 0 <= x }-> EqualProp {v:Integer | v < 0 } (add1Int x) (add1Nat x) @-}
pf0BadRange x = extensionality (add1Int x) (add1Nat x) ()

pfBadDomain :: () -> EqualityProp (Integer -> Integer)
{-@ fail pfBadDomain @-}
{-@ pfBadDomain :: () -> EqualProp (x:Integer -> Integer) add1Int add1Nat @-}
pfBadDomain _ = eqFun add1Int add1Nat (\x -> eqSMT (add1Int x) (add1Nat x) ())

pf0BadDomain :: Integer -> EqualityProp Integer
{-@ fail pf0BadDomain @-}
{-@ pf0BadDomain :: x:Integer-> EqualProp Integer {add1Int x} (add1Nat x) @-}
pf0BadDomain x = eqSMT (add1Int x) (add1Nat x) () 
-}

--------------------------------------------------------------------------------
-- | Definitions for add1Int and g
--------------------------------------------------------------------------------

{-@ reflect add1Int @-}
add1Int :: Integer -> Integer 
add1Int x = x + 1 

{-@ reflect add1Nat @-}
add1Nat :: Integer -> Integer 
add1Nat x = if x >= 0 then x + 1 else 0
