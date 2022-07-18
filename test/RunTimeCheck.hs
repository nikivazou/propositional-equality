{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module RunTimeCheck where 

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++))
import Relation.Equality.Prop


{-@ critical :: {x:a | slowSpec x } -> a @-}
critical :: a -> a 
critical x = x 

{-@ bar :: EqualProp (a -> Bool) {fastSpec} {slowSpec} -> a -> Maybe a @-}
bar :: EqualityProp (a -> Bool) -> a -> Maybe a 
bar pf x = if fastSpec x ? concreteness (fastSpec x) (slowSpec x) (unExt x pf)
            then Just (critical x)
            else Nothing 

{-@ unExt :: x:a -> EqualProp (a -> Bool) {fastSpec} {slowSpec} -> EqualProp Bool {fastSpec x} {slowSpec x} @-}
unExt :: a -> EqualityProp (a -> Bool) -> EqualityProp Bool 
unExt x p = substitutability (flip' x) fastSpec slowSpec p  ? flip' x fastSpec ? flip' x slowSpec 



{-@ reflect flip' @-}
flip' :: a -> (a -> b) -> b
flip' x f = f x  

{-@ reflect fastSpec @-}
fastSpec :: a -> Bool
fastSpec _ = True 

{-@ reflect slowSpec @-}
slowSpec :: a -> Bool
slowSpec _ = True  