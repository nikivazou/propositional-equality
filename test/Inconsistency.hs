module Inconsistency where 

import Function 
import Relation.Equality.Prop
import Data.Refined.Unit 
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (map)

-- | Seciton 2: Functional extensionality is inconsistent in Refinement Types 

{-@ assume funExt :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x = g x}) -> {f = g} @-}
funExt :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
funExt _ _ _ = ()


{-@ reflect incrInt @-}
{-@ reflect incrPos @-}
incrInt :: Integer -> Integer
incrPos :: Integer -> Integer
incrInt n = n + 1
incrPos n = if 0 < n then n + 1 else 0 

{-@ ple incrSamePos @-}
{-@ type Pos = {n:Integer | 0 < n } @-}
{-@ incrSamePos :: n:Pos -> {incrPos n = incrInt n} @-}
incrSamePos :: Integer -> ()
incrSamePos _ = ()


{-@ incrExt :: () -> { incrPos = incrInt } @-}
incrExt :: () -> ()
incrExt _ = funExt incrPos incrInt incrSamePos 

{-@ incrMap :: xs:[Integer] -> {map incrPos xs = map incrInt xs} @-}
incrMap :: [Integer] -> ()
incrMap xs = incrExt ()

{-@ ple inconsistencyI @-}
{-@ inconsistencyI :: () -> {incrPos (0-5) = incrInt (0-5)} @-}
inconsistencyI :: () -> ()
inconsistencyI _ = incrExt ()


{-@ reflect plus2 @-}
plus2 :: Integer -> Integer
plus2 x = x + 2 


{-@ type Empty = {v:Integer | false } @-}
{-@ ple incrSameEmpty @-}
incrSameEmpty :: Integer -> ()
{-@ incrSameEmpty :: n:Empty -> {incrInt n = plus2 n} @-}
incrSameEmpty _ = ()

{-@ incrPlus2Ext :: () -> { incrInt = plus2 } @-}
incrPlus2Ext :: () -> ()
incrPlus2Ext _ = funExt incrInt plus2 incrSameEmpty

inconsistencyII :: () -> () 
{-@ inconsistencyII :: () -> { incrInt 0 = plus2 0 } @-} 
inconsistencyII _ = incrPlus2Ext ()


-- | 2.1 Refined, Type-Indexed, Extensional Propositional Equality
-- | We use extensionality instead of xEq 


-- ACCEPTED AND POSSIBLE
{-@ incrExtGood :: () -> PEq (Pos -> Integer) {incrPos} {incrInt} @-}
incrExtGood :: () -> EqualityProp (Integer -> Integer)
incrExtGood _ = extensionality incrPos incrInt incrEq 

incrEq :: Integer -> EqualityProp Integer
{-@ incrEq :: n:Pos -> PEq Integer {incrPos n} {incrInt n} @-}
{-@ ple incrEq @-}
incrEq n = refl (incrPos n)


-- ACCEPTED AND IMPOSSIBLE
{-@ incrExtGood2 :: () -> PEq (Pos -> Integer) {incrPos} {incrInt} @-}
incrExtGood2 :: () -> EqualityProp (Integer -> Integer)
incrExtGood2 _ = extensionality incrPos incrInt incrEq2

incrEq2  :: Integer -> EqualityProp Integer
{-@ incrEq2 :: n:Integer -> PEq Integer {incrPos n} {incrInt n} @-}
incrEq2 n = undefined  -- IMPOSSIBLE TO CONSTRUCT THIS TERM  -- reflexivity (incrPos n)


-- REJECTED AND POSSIBLE

{-@ fail incrExtGood3 @-}
{-@ incrExtGood3 :: () -> PEq (Pos -> Integer) {incrPos} {incrInt} @-}
incrExtGood3 :: () -> EqualityProp (Integer -> Integer)
incrExtGood3 _ = extensionality incrPos incrInt incrEq3 -- REJECTED!

incrEq3  :: Integer -> EqualityProp Integer
{-@ incrEq3 :: n:Empty -> PEq Integer {incrPos n} {incrInt n} @-}
incrEq3 n = refl (incrPos n)

-- | We use substitutability instead of subst 

{-@ incrMapProp :: () -> PEq ([Pos] -> [Integer]) {map incrPos} {map incrInt} @-}
incrMapProp :: () -> EqualityProp ([Integer] -> [Integer])
incrMapProp _ = substitutability map incrPos incrInt (incrExtGood ())



{-@ retract :: f:(a -> b) -> g:(a -> b) -> PEq (a -> b) {f} {g} 
            -> x:a -> PEq b {f x} {g x} @-}
retract :: (a -> b) -> (a -> b) -> EqualityProp (a -> b) -> a -> EqualityProp b 
retract f g peq x = substitutability (given x) f g peq ? given x f ? given x g


{-@ goodFO :: x:{Integer | 42 < x } -> PEq Integer {incrPos x} {incrInt x}  @-}
goodFO :: Integer -> EqualityProp Integer 
goodFO x = retract incrPos incrInt (incrExtGood ()) x 

{-@ fail badFO @-}
{-@ badFO :: () -> PEq Integer {incrPos 0} {incrInt 0}  @-}
badFO :: () -> EqualityProp Integer 
badFO _ = retract incrPos incrInt (incrExtGood ()) 0 