{-# LANGUAGE BlockArguments #-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fast"        @-}

module Readers where

import Data.Refined.Unit
import Function hiding (compose)
import Language.Haskell.Liquid.ProofCombinators
import Relation.Equality.Prop
import Prelude hiding (fmap, id, pure, (<$>), (<*>), (>>=))

type Reader a b = a -> b

{-@ reflect fmap @-}
fmap :: (a -> b) -> Reader r a -> Reader r b
fmap fab fra r = fab (fra r)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect dollar @-}
dollar :: (a -> b) -> a -> b
dollar f v = f v

{-@ reflect on @-}
on :: a -> (a -> b) -> b
on v f = f v

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> (a -> c)
compose g f x = g (f x)

functorLaw_identity :: Equality a => EqualityProp (Reader r a -> Reader r a)
{-@ functorLaw_identity :: Equality a -> EqualProp (Reader r a -> Reader r a) (fmap id) id @-}
functorLaw_identity =
  extensionality
    (fmap id)
    id
    ( \r ->
        extensionality
          (fmap id r)
          (id r)
          ( \a ->
              reflexivity (fmap id r a)
                ? ( fmap id r a
                      =~= id (r a)
                      =~= id r a
                      *** QED
                  )
          )
    )

functorLaw_composition :: Equality c => (a -> b) -> (b -> c) -> EqualityProp (Reader r a -> Reader r c)
{-@ functorLaw_composition :: Equality c => f:(a -> b) -> g:(b -> c) ->
      EqualProp (Reader r a -> Reader r c) (fmap (compose g f)) (compose (fmap g) (fmap f)) @-}
functorLaw_composition f g =
  extensionality
    (fmap (compose g f))
    (compose (fmap g) (fmap f))
    ( \rdr ->
        extensionality
          (fmap (compose g f) rdr)
          ((compose (fmap g) (fmap f)) rdr)
          ( \r ->
              reflexivity
                (fmap (compose g f) rdr r)
                ? ( fmap (compose g f) rdr r
                      =~= (compose g f) (rdr r)
                      =~= g (f (rdr r))
                      =~= g (((fmap f) rdr) r)
                      =~= fmap g ((fmap f) rdr) r
                      =~= (compose (fmap g) (fmap f)) rdr r
                      *** QED
                  )
          )
    )

{-@ reflect pure @-}
pure :: a -> Reader r a
pure a _r = a

{-@ reflect ap @-}
ap :: Reader r (a -> b) -> Reader r a -> Reader r b
ap frab fra r = frab r (fra r)

applicativeLaw_identity :: Equality a => Reader r a -> EqualityProp (Reader r a)
{-@ applicativeLaw_identity :: Equality a => v:Reader r a ->
      EqualProp (Reader r a) (ap (pure id) v) v @-}
applicativeLaw_identity v =
  extensionality
    (ap (pure id) v)
    v
    ( \r ->
        transitivity
          (ap (pure id) v r)
          ((pure id) r (v r))
          (v r)
          (reflexivity (ap (pure id) v r))
          ( transitivity
              ((pure id) r (v r))
              (id (v r))
              (v r)
              (reflexivity ((pure id) r (v r)))
              (reflexivity (id (v r)))
          )
    )

applicativeLaw_homomorphism :: Equality b => (a -> b) -> a -> EqualityProp (Reader r b)
{-@ applicativeLaw_homomorphism :: Equality b => f:(a->b) -> v:a ->
      EqualProp (Reader r b) (ap (pure f) (pure v)) (pure (f v)) @-}
applicativeLaw_homomorphism f v =
  extensionality
    (ap (pure f) (pure v))
    (pure (f v))
    ( \r ->
        transitivity
          (ap (pure f) (pure v) r)
          (pure f r (pure v r))
          (pure (f v) r)
          (reflexivity (ap (pure f) (pure v) r))
          ( transitivity
              (pure f r (pure v r))
              (pure f r v)
              (pure (f v) r)
              (reflexivity (pure f r (pure v r)))
              ( transitivity
                  (pure f r v)
                  (f v)
                  (pure (f v) r)
                  (reflexivity (pure f r v))
                  (reflexivity (f v))
              )
          )
    )

applicativeLaw_interchange :: Equality b => Reader r (a -> b) -> a -> EqualityProp (Reader r b)
{-@ applicativeLaw_interchange :: Equality b => u:(Reader r (a -> b)) -> y:a ->
      EqualProp (Reader r b) (ap u (pure y)) (ap (pure (on y)) u) @-}
applicativeLaw_interchange u y =
  extensionality
    (ap u (pure y))
    (ap (pure (on y)) u)
    ( \r ->
        transitivity
          (ap u (pure y) r)
          (u r (pure y r))
          (ap (pure (on y)) u r)
          (reflexivity (ap u (pure y) r))
          ( transitivity
              (u r (pure y r))
              (u r y)
              (ap (pure (on y)) u r)
              (reflexivity (u r (pure y r)))
              ( transitivity
                  (u r y)
                  ((on y) (u r))
                  (ap (pure (on y)) u r)
                  (reflexivity (u r y))
                  ( transitivity
                      ((on y) (u r))
                      ((pure (on y)) r (u r))
                      (ap (pure (on y)) u r)
                      (reflexivity ((on y) (u r)))
                      (reflexivity ((pure (on y)) r (u r)))
                  )
              )
          )
    )

--- WHEW this one takes a long time
applicativeLaw_composition ::
  Equality c =>
  Reader r (b -> c) ->
  Reader r (a -> b) ->
  Reader r a ->
  EqualityProp (Reader r c)
{-@ applicativeLaw_composition :: Equality c =>
      u:(Reader r (b -> c)) -> v:(Reader r (a -> b)) -> w:(Reader r a) ->
      EqualProp (Reader r c) (ap (ap (ap (pure compose) u) v) w) (ap u (ap v w)) @-}
applicativeLaw_composition u v w =
  extensionality
    (ap (ap (ap (pure compose) u) v) w)
    (ap u (ap v w))
    ( \r ->
        transitivity
          (ap (ap (ap (pure compose) u) v) w r)
          ((ap (ap (pure compose) u) v) r (w r))
          (ap u (ap v w) r)
          (reflexivity (ap (ap (ap (pure compose) u) v) w r))
          ( transitivity
              ((ap (ap (pure compose) u) v) r (w r))
              ((ap (pure compose) u) r (v r) (w r))
              (ap u (ap v w) r)
              (reflexivity ((ap (ap (pure compose) u) v) r (w r)))
              ( transitivity
                  ((ap (pure compose) u) r (v r) (w r))
                  ((pure compose) r (u r) (v r) (w r))
                  (ap u (ap v w) r)
                  (reflexivity ((ap (pure compose) u) r (v r) (w r)))
                  ( transitivity
                      ((pure compose) r (u r) (v r) (w r)) -- skipped ((\_r -> compose) r (u r) (v r) (w r))
                      (compose (u r) (v r) (w r))
                      (ap u (ap v w) r)
                      (reflexivity ((pure compose) r (u r) (v r) (w r)))
                      ( transitivity
                          (compose (u r) (v r) (w r))
                          ((u r) ((v r) (w r)))
                          (ap u (ap v w) r)
                          (reflexivity (compose (u r) (v r) (w r)))
                          ( transitivity
                              ((u r) ((v r) (w r)))
                              (u r (v r (w r)))
                              (ap u (ap v w) r)
                              (reflexivity ((u r) ((v r) (w r))))
                              ( transitivity
                                  (u r (v r (w r)))
                                  (u r (ap v w r))
                                  (ap u (ap v w) r)
                                  (reflexivity (u r (v r (w r))))
                                  (reflexivity (u r (ap v w r)))
                              )
                          )
                      )
                  )
              )
          )
    )


ap_fmap :: Equality b => (a -> b) -> Reader r a -> EqualityProp (Reader r b)
{-@ ap_fmap :: f:(a -> b) -> a:(Reader r a) -> EqualProp (Reader r b) (fmap f a) (ap (pure f) a) @-}
ap_fmap f a =
  extensionality
    (fmap f a)
    (ap (pure f) a)
    ( \r ->
        transitivity
          (fmap f a r)
          (f (a r))
          (ap (pure f) a r)
          (reflexivity (fmap f a r))
          ( transitivity
              (f (a r))
              ((pure f) r (a r))
              (ap (pure f) a r)
              (reflexivity (f (a r)))
              (reflexivity ((pure f) r (a r)))
          )
    )


{-@ reflect bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind fra farb = \r -> farb (fra r) r

monadLaw_leftIdentity :: Equality b => a -> (a -> Reader r b) -> EqualityProp (Reader r b)
{-@ monadLaw_leftIdentity :: Reflexivity b => a:a -> f:(a -> Reader r b) ->
      EqualProp (Reader r b) (bind (pure a) f) (f a)
@-}
monadLaw_leftIdentity a f =
  extensionality
    (bind (pure a) f)
    (f a)
    ( \r ->
        transitivity
          (bind (pure a) f r)
          (f (pure a r) r)
          (f a r)
          (reflexivity (bind (pure a) f r))
          (reflexivity (f (pure a r) r))
    )

monadLaw_leftIdentity' :: Equality b => a -> (a -> Reader r b) -> EqualityProp (Reader r b)
{-@ monadLaw_leftIdentity' :: Reflexivity b => a:a -> f:(a -> Reader r b) ->
      EqualProp (Reader r b) (bind (pure a) f) (f a)
@-}
monadLaw_leftIdentity' a f =
  extensionality
    (bind (pure a) f)
    (f a)
    ( \r ->
        reflexivity (bind (pure a) f r)
          ? (bind (pure a) f r =~= f (pure a r) r *** QED)
    )

monadLaw_rightIdentity :: Equality a => (Reader r a) -> EqualityProp (Reader r a)
{-@ monadLaw_rightIdentity :: Equality a => m:(Reader r a) -> EqualProp (Reader r a) (bind m pure) m @-}
monadLaw_rightIdentity m =
  extensionality
    (bind m pure)
    m
    ( \r ->
        reflexivity (bind m pure r)
          ? ( (bind m pure r)
                =~= pure (m r) r
                *** QED
            )
    )

{-@ reflect kleisli @-}
kleisli :: (a -> Reader r b) -> (b -> Reader r c) -> a -> Reader r c
kleisli f g x = bind (f x) g

monadLaw_associativity ::
  Equality c => (Reader r a) -> (a -> Reader r b) -> (b -> Reader r c) -> EqualityProp (Reader r c)
{-@ monadLaw_associativity :: Equality c =>
      m:(Reader r a) -> f:(a -> Reader r b) -> g:(b -> Reader r c) ->
      EqualProp (Reader r c) (bind (bind m f) g) (bind m (kleisli f g))
@-}
monadLaw_associativity m f g =
  extensionality
    (bind (bind m f) g)
    (bind m (kleisli f g))
    ( \r ->
        let el = bind (bind m f) g r
            eml = g (bind m f r) r
            em = (bind (f (m r)) g) r
            emr = kleisli f g (m r) r
            er = bind m (kleisli f g) r
         in transitivity
              el
              em
              er
              (transitivity el eml em (reflexivity el) (reflexivity eml))
              (transitivity em emr er (reflexivity em) (reflexivity emr))
    )