{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}

module Reverse where

import Data.Refined.Unit
import Function hiding (compose)
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (fmap, id, pure, (++), (<$>), (<*>), (>>=))

{-@ infix ++ @-}
{-@ infix :  @-}

------------------------------------------------------------

-- | Main Theorem   ----------------------------------------

------------------------------------------------------------
-- This is SAFE
theoremFirstStyle :: AEq [a] => EqualityProp ([a] -> [a])
{-@ theoremFirstStyle :: EqualProp ([a] -> [a]) {fastReverse} {slowReverse} @-}
theoremFirstStyle = extensionality fastReverse slowReverse reverseTEq

{-@ reverseTEq :: AEq [a] => xs:[a] -> EqualProp [a] {fastReverse xs} {slowReverse xs} @-}
reverseTEq :: AEq [a] => [a] -> EqualityProp [a]
reverseTEq xs = baseEq (fastReverse xs) (slowReverse xs) ((reverseEq xs) ? reflP (fastReverse xs))

theoremSecondStyle :: AEq [a] => EqualityProp ([a] -> [a])
{-@ theoremSecondStyle :: AEq [a] => EqualProp ([a] -> [a]) {fastReverse} {slowReverse} @-}
theoremSecondStyle = extensionality fastReverse slowReverse reverseTEq

-- on arbitrary types, uses explicit lemma
reverseFunProp :: (Equality [a], Equality [a]) => [a] -> EqualityProp [a]
{-@ reverseFunProp :: (Equality [a], Equality [a]) => xs:[a] -> EqualProp [a] {fastReverse xs} {slowReverse xs} @-}
reverseFunProp xs =
  transitivity
    (fastReverse xs)
    (slowReverse xs ++ [])
    (slowReverse xs)
    (reverseSameLemma [] xs)
    (rightIdP (slowReverse xs))


reverseSameLemma :: (Equality [a], Equality [a]) => [a] -> [a] -> EqualityProp [a]
{-@ reverseSameLemma :: (Equality [a], Equality [a]) => rest:[a] -> xs:[a] -> EqualProp [a] {fastReverse' rest xs} {slowReverse xs ++ rest} @-}
reverseSameLemma rest [] = reflexivity rest
reverseSameLemma rest (x : xs) =
  transitivity
    (fastReverse' rest (x : xs))
    (slowReverse xs ++ (x : rest))
    (slowReverse (x : xs) ++ rest)
    (reverseSameLemma (x : rest) xs)
    (assocP (slowReverse xs) [x] rest)

{-@ rightIdP :: xs:[a] -> EqualProp [a] {xs ++ []} {xs} @-}
rightIdP :: (Equality [a], Equality [a]) => [a] -> EqualityProp [a]
rightIdP [] = reflexivity []
rightIdP (x : xs) =
  transitivity
    ((x : xs) ++ [])
    (cons x (xs ++ []))
    (cons x xs)
    (reflexivity (x : (xs ++ [])))
    (eqRTCtx (xs ++ []) (xs) (rightIdP xs) (cons x))

{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a]
          -> EqualProp [a] {(xs ++ (ys ++ zs))} {((xs ++ ys) ++ zs)}  @-}
assocP :: (Equality [a], Equality [a]) => [a] -> [a] -> [a] -> EqualityProp [a]
assocP [] ys zs = reflexivity ([] ++ (ys ++ zs))
assocP (x : xs) ys zs =
  transitivity
    ((x : xs) ++ (ys ++ zs))
    (cons x (xs ++ (ys ++ zs)))
    (cons x ((xs ++ ys) ++ zs))
    (reflexivity ((x : xs) ++ (ys ++ zs)))
    (eqRTCtx ((xs ++ (ys ++ zs))) ((xs ++ ys) ++ zs) (assocP xs ys zs) (cons x))


{-@ reflect cons @-}
cons :: a -> [a] -> [a]
{-@ cons :: x:a -> y:[a] -> {v:[a] | v == x:y} @-}
cons x xs = x : xs

{-@ consP :: x:a -> xs:[a] -> {cons x xs == x:xs} @-}
consP :: a -> [a] -> ()
consP x xs = cons x xs *** QED

reverseOneSwoopEq :: AEq [a] => EqualityProp ([a] -> [a])
{-@ reverseOneSwoopEq :: AEq [a] => EqualProp ([a] -> [a]) {fastReverse} {slowReverse} @-}
reverseOneSwoopEq = extensionality fastReverse slowReverse $ \xs ->
  baseEq (fastReverse xs) (slowReverse xs) (reverseEq xs ? reflP (fastReverse xs))

{-@ reverseEq :: xs:[a] -> { fastReverse xs = slowReverse xs } @-}
reverseEq :: [a] -> ()
reverseEq xs =
  lemma xs []
    ? rightId (slowReverse xs)

{-@ reverseNoEq :: xs:[a] -> { fastReverse xs = slowReverse xs } @-}
reverseNoEq :: [a] -> ()
reverseNoEq xs =
  fastReverse xs
    ? fastReverse' [] xs
    ? lemma xs []
    ? rightId (slowReverse xs)
    ? slowReverse xs
    *** QED

------------------------------------------------------------

-- | Bad proofs that should fail  --------------------------

------------------------------------------------------------


{-
reverseFunEqWrong :: Eq a => EqualityProp ([a] -> [a])
{-@ fail reverseFunEqWrong @-}
{-@ reverseFunEqWrong :: Eq a => EqRT ([a] -> [a]) (fastReverse) (badReverse) @-}
reverseFunEqWrong = eqFun fastReverse slowReverse trivialTEq

-- this shouldn't be provable! we're sending the wrong goals to SMT :(
reverseFunEqDistressing :: Eq a => EqualityProp ([a] -> [a])
{-@ fail reverseFunEqDistressing @-}
{-@ reverseFunEqDistressing :: Eq a => EqRT ([a] -> [a]) (fastReverse) (badReverse) @-}
reverseFunEqDistressing = eqFun fastReverse badReverse trivialTEq

-- this shouldn't be provable... so easily.
reverseFunEqTooGood :: Eq a => EqualityProp ([a] -> [a])
{-@ fail reverseFunEqTooGood @-}
{-@ reverseFunEqTooGood :: Eq a => EqRT ([a] -> [a]) (fastReverse) (slowReverse) @-}
reverseFunEqTooGood = eqFun fastReverse slowReverse trivialTEq

{-@ trivialTEq :: Eq a => xs:[a] -> EqRT [a] (xs) (xs) @-}
trivialTEq :: Eq a => [a] -> EqualityProp [a]
trivialTEq xs = fromEqSMT xs xs ()

{-@ reverseFunNoExt :: { fastReverse = slowReverse } @-}
{-@ fail reverseFunNoExt @-}
reverseFunNoExt :: ()
reverseFunNoExt = () ? reverseNoEq
-}
------------------------------------------------------------

-- | Helper Proofs  ----------------------------------------

------------------------------------------------------------

{-
Note: All the below are proved by SMT and without any `Eq [a]`
-}

{-@ lemma :: xs:[a] -> ys:[a]
          -> { fastReverse' ys xs = slowReverse xs ++ ys } @-}
lemma :: [a] -> [a] -> ()
lemma [] _ = ()
lemma (x : xs) ys =
  lemma xs (x : ys)
    ? assoc (slowReverse xs) [x] ys

{-@ rightId :: xs:[a] -> { xs ++ [] = xs } @-}
rightId :: [a] -> ()
rightId [] = ()
rightId (_ : xs) = rightId xs

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
          -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _ = ()
assoc (_ : xs) ys zs = assoc xs ys zs

------------------------------------------------------------

-- | Code --------------------------------------------------

------------------------------------------------------------

{-@ reflect fastReverse @-}
fastReverse :: [a] -> [a]
fastReverse xs = fastReverse' [] xs

{-@ reflect fastReverse' @-}
fastReverse' :: [a] -> [a] -> [a]
fastReverse' acc [] = acc
fastReverse' acc (x : xs) = fastReverse' (x : acc) xs

{-@ reflect slowReverse @-}
slowReverse :: [a] -> [a]
slowReverse [] = []
slowReverse (x : xs) = slowReverse xs ++ [x]

{-@ reflect badReverse @-}
badReverse :: [a] -> [a]
badReverse xs = xs

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)
