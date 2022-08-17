module Syntax.EqReasoning

import Syntax.PreorderReasoning

infixl 0 ~=
public export
(~=) : FastDerivation x y -> (0 z : dom) -> {auto xEqy : y = z} -> FastDerivation x z
(~=) deriv y {xEqy} = deriv ~~ y ...(xEqy) -- Beats writing ...(Refl) time and time again

