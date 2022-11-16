module Book.Part3.Soundness2

import Book.Part3.Soundness
import Book.Part3.Compositional
import Book.Part3.Denotational
import Book.Part2.Untyped
import Book.Appendix.Substitution
import Control.Function.FunExt


-- Breaking the module for totality checking quickness purposes

public export
reflect : FunExt => {env : Env ctx} -> {m, m', n : _} -> {v : _}
  -> env |- (n, v) -> m -=> m' -> m' = n
  -> env |- (m, v)
reflect Var y m'EqN = case y of
  (IntroAppLeft x) => case m'EqN of {}
  (IntroAppRight x) => case m'EqN of {}
  BetaLam => reflectBeta (rewrite m'EqN in Var)
  (IntroLam x) => case m'EqN of {}
reflect (FunElim x z) (IntroAppLeft y) Refl = FunElim (reflect x y Refl) z
reflect (FunElim x z) (IntroAppRight y) Refl = FunElim x (reflect z y Refl)
reflect (FunElim x z) BetaLam m'EqN = reflectBeta (rewrite m'EqN in FunElim x z)
reflect (FunElim _ _) (IntroLam _) m'EqN = case m'EqN of {}
reflect (FunIntro x) (IntroAppLeft y) m'EqN = case m'EqN of {}
reflect (FunIntro x) (IntroAppRight y) m'EqN = case m'EqN of {}
reflect (FunIntro x) BetaLam m'EqN = reflectBeta (rewrite m'EqN in FunIntro x)
reflect (FunIntro x) (IntroLam y) Refl = FunIntro (reflect x y Refl)
reflect BotIntro y m'EqN = BotIntro
reflect (UIntro x z) y m'EqN = UIntro (reflect x y (rewrite m'EqN in Refl)) (reflect z y (rewrite m'EqN in Refl))
reflect (Sub x z) y m'EqN = Sub (reflect x y m'EqN) z

reduceEqual : FunExt => {m, n : _} -> m -=> n -> Denote m == Denote n
reduceEqual r env v = (\ m => preserve m r, \ n => reflect n r Refl)

public export
soundness : FunExt => {m, n : _} -> m -=>> n -> Denote m == Denote n
soundness Refl env v = (\x => x, \x => x)
soundness (x `Trans` y) env v = (reduceEqual x `trans` soundness y) env v
