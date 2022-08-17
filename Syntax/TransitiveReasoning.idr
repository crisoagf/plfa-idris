module Syntax.TransitiveReasoning

import Control.Relation
import Control.Order
import Syntax.PreorderReasoning.Generic

public export
data FastDerivation : (leq : a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  (<~) : {x, y : a}
         -> Syntax.PreorderReasoning.Generic.FastDerivation leq x y -> {z : a} -> (step : Step leq y z)
         -> FastDerivation leq x z

public export
CalcWith' : Transitive dom leq => {0 x : dom} -> {0 y : dom} -> Syntax.TransitiveReasoning.FastDerivation leq x y -> x `leq` y
CalcWith' ((<~) (|~ x) (z ... step)) = step
CalcWith' ((<~) ((<~) der (y ... step1)) (z ... step2)) = transitive {rel = leq} (CalcWith' ((<~) der (y ... step1))) step2

infixl 0 ~=
public export
(~=) : Preorder dom rel => Syntax.PreorderReasoning.Generic.FastDerivation rel x y -> (z : dom) -> {auto xEqy : y = z} -> Syntax.PreorderReasoning.Generic.FastDerivation rel x z
(~=) deriv y {xEqy} = deriv ~~ y ...(xEqy) -- Beats writing ...(Refl) time and time again

