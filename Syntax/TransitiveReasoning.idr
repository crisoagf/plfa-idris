module Syntax.TransitiveReasoning

import Control.Relation
import Syntax.PreorderReasoning.Generic

public export
isNonTrivial : DerivationType der -> Type
isNonTrivial TrivialDerivation = Void
isNonTrivial SingleStepDerivation = ()
isNonTrivial NonTrivialDerivation = ()

0
nonTrivialRecursive : isNonTrivial (derivationType (der <~ step))
nonTrivialRecursive {der = (|~ x)} = ()
nonTrivialRecursive {der = (x <~ y)} = ()

explicitTrans : {0 leq : a -> a -> Type} -> (trans : {x,y,z : a} -> x `leq` y -> y `leq` z -> x `leq` z) -> Transitive a leq
explicitTrans trans = MkTransitive trans

-- Because sometimes you want to use a transitive order on stuff that can't have an instance (like a subset of the functions space)
public export
ExplicitCalc : {0 x : dom} -> {0 y : dom} -> (trans : {x0, y0, z0 : dom} -> x0 `leq` y0 -> y0 `leq` z0 -> x0 `leq` z0) -> (der : FastDerivation leq x y) -> {auto 0 nonTrivial : isNonTrivial (derivationType der)} -> x `leq` y
ExplicitCalc {x} trans der with (derivationType der, isNonTrivial (derivationType der))
  ExplicitCalc {x} trans (|~ _) | (TrivialDerivation, w) impossible
  ExplicitCalc {x} trans (|~ x <~ step) | (SingleStepDerivation, w) = CalcSmart (|~ x <~ step)
  ExplicitCalc {x} trans ((der <~ step1) <~ step2) | (NonTrivialDerivation, w) = CalcSmart @{explicitTrans trans} (der <~ step1 <~ step2)
