{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--ple"         @-}

module Endofunctors where

-- macros

import Data.Refined.Unit
import Function
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (id, mappend, mempty)

type Endo a = a -> a

{-@ reflect mempty @-}
mempty :: Endo a
mempty a = a

{-@ reflect mappend @-}
mappend :: Endo a -> Endo a -> Endo a
mappend f g a = f (g a)

{-
(x <> y) <> z = x <> (y <> z) -- associativity
mempty <> x = x               -- left identity
x <> mempty = x               -- right identity
-}

{-@ monoid_leftIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {mappend mempty x} {x} @-}
monoid_leftIdentity :: Reflexivity a => (Endo a) -> EqualityProp (Endo a)
monoid_leftIdentity x =
  extensionality (mappend mempty x) x $ \a ->
    refl (mappend mempty x a)
      ? ( mappend mempty x a
            =~= mempty (x a)
            =~= x a
            *** QED
        )

{-@ monoid_rightIdentity :: Reflexivity a => x:(Endo a) -> EqualProp (Endo a) {x} {mappend x mempty} @-}
monoid_rightIdentity :: Reflexivity a => Endo a -> EqualityProp (Endo a)
monoid_rightIdentity x =
  extensionality x (mappend x mempty) $ \a ->
    refl (x a)
      ? ( x a -- (mappend x mempty a)
            =~= x (mempty a)
            =~= mappend x mempty a
            *** QED
        )

{-@ monoid_associativity :: Reflexivity a =>
      x:(Endo a) -> y:(Endo a) -> z:(Endo a) ->
      EqualProp (Endo a) {mappend (mappend x y) z} {mappend x (mappend y z)} @-}
monoid_associativity :: Reflexivity a => Endo a -> Endo a -> Endo a -> EqualityProp (Endo a)
monoid_associativity x y z =
  extensionality (mappend (mappend x y) z) (mappend x (mappend y z)) $ \a ->
    refl (mappend (mappend x y) z a)
      ? ( mappend (mappend x y) z a
            =~= (mappend x y) (z a)
            =~= x (y (z a))
            =~= x (mappend y z a)
            =~= mappend x (mappend y z) a
            *** QED
        )
