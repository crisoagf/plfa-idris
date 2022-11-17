module Syntax.TransitiveReasoning

import Syntax.PreorderReasoning.Generic

-- Because sometimes you want to use a transitive order on stuff that can't have an instance (like a subset of the functions space)
public export
ExplicitCalc : {0 x : dom} -> {0 y : dom} -> (trans : {x0, y0, z0 : dom} -> x0 `leq` y0 -> y0 `leq` z0 -> x0 `leq` z0) -> (deriv : FastDerivation leq x y) -> {auto nonTrivial : derivationType deriv = NonTrivialDerivation} -> x `leq` y
ExplicitCalc trans ((<~) (|~ x) (z ... step)) = step
ExplicitCalc trans ((<~) ((<~) der (y ... step1)) (z ... step2)) = trans (ExplicitCalc trans ((<~) der (y ... step1))) step2
