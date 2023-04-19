module Book.Part2.BigStep

import Book.Part2.Confluence
import Book.Part2.Untyped
import Book.Appendix.Substitution
import Control.Function.FunExt

public export
ClosEnv : Context -> Type

public export
data Clos : Type where
  MkClos : {ctx : Context} -> (m : ctx |- Star) -> ClosEnv ctx -> Clos

ClosEnv ctx = (x : ctx `Has` Star) -> Clos

public export
Empty : ClosEnv Empty
Empty x impossible

public export
(:<) : {ctx : Context} -> ClosEnv ctx -> Clos -> ClosEnv (ctx :< Star)
(:<) f y Z = y
(:<) f y (S x) = f x

public export
data (|-) : ClosEnv ctx -> (ctx |- Star, Clos) -> Type where
  CVar : {x : _} -> {ctx : _} -> {m : ctx |- _} -> {env' : _} -> env x = MkClos {ctx} m env' -> env' |- (m, clos) -> env |- (Var x, clos)
  CLam : env |- (Lam m, MkClos (Lam m) env)
  CApp : {ctx : _} -> {ctx' : _} -> {env : ClosEnv ctx} -> {l, m : _} -> {n : ctx' :< Star |- Star} -> {env' : ClosEnv ctx'} -> env |- (l, MkClos (Lam n) env') -> (env' :< MkClos m env) |- (n, clos)
      -> env |- (l `App` m, clos)

public export
bigStepDet : env |- (m, clos) -> env |- (m, clos') -> clos = clos'
bigStepDet (CVar prf x) (CVar prf1 y) with (sym prf `trans` prf1)
  bigStepDet (CVar prf x) (CVar prf1 y) | Refl = bigStepDet x y
bigStepDet CLam CLam = Refl
bigStepDet (CApp x z) (CApp y w) with (bigStepDet x y)
  bigStepDet (CApp x z) (CApp y w) | Refl = bigStepDet z w

Closes : Clos -> Empty |- Star -> Type
EnvFor : {ctx : _} -> ClosEnv ctx -> Subst ctx Empty -> Type

MkClos {ctx} m env `Closes` n = (sigma : Subst ctx Empty ** (env `EnvFor` sigma, n = subst sigma m))
env `EnvFor` sigma = {x : _} -> env x `Closes` sigma x

envId : Empty `EnvFor` Substitution.ids
envId impossible

extSubst : Subst ctx ctx' -> ctx' |- Star -> Subst (ctx :< Star) ctx'
extSubst sigma n = subst (substZero n) . exts sigma

substZeroExts : FunExt
  => {sigma : Subst ctx ctx'} -> {m : _} -> (subst (substZero m) . exts sigma) (S x) = sigma x
substZeroExts = cong (\ f => f (S x)) (substZeroExtsCons {sigma} {m})

envExt : FunExt => {sigma : Subst ctx Empty}
   -> env `EnvFor` sigma -> clos `Closes` n -> (env :< clos) `EnvFor` extSubst sigma n
envExt f y {x = Z} = y
envExt f y {x = (S x)} = rewrite substZeroExts {sigma} {m = n} {x} in f

unstuck : (env : ClosEnv ctx) -> (x : ctx `Has` Star) -> (ctx' : Context ** (mclos : (ctx' |- Star, ClosEnv ctx') ** env x = MkClos {ctx = ctx'} (fst mclos) (snd mclos)))
unstuck {ctx = ctx'} env x with (env x)
  unstuck {ctx = ctx'} env x | (MkClos {ctx = ctx''} m f) = (ctx'' ** ((m, f) ** Refl))

closureReduces : FunExt
  => {ctx : _}
  -> {env : ClosEnv ctx}
  -> {sigma : Subst ctx Empty}
  -> {m : ctx |- Star}
  -> {clos : Clos}
  -> env |- (m, clos) -> env `EnvFor` sigma -> (n : Empty |- Star ** (subst sigma m -=>> n, clos `Closes` n))
closureReduces {m = Var x} (CVar {ctx} {x} prf y) f with (unstuck env x)
  closureReduces {m = Var x} (CVar {ctx} {x} prf y) f | (MkDPair tau (MkDPair z snd)) with (sym snd `trans` prf)
    closureReduces {m = Var x} (CVar {ctx} {x} prf y) f | (MkDPair ctx (MkDPair z snd)) | Refl with (replace {p = \ expr => Closes expr (sigma x)} snd (f {x}))
      closureReduces {m = Var x} (CVar {ctx = ctx} {x = x} prf y) f | (MkDPair ctx (MkDPair z snd)) | Refl | (MkDPair tau (w, v)) with (closureReduces {sigma = tau} y w)
        closureReduces {m = Var x} (CVar {ctx = ctx} {x = x} prf y) f | (MkDPair ctx (MkDPair z snd)) | Refl | (MkDPair tau (w, v)) | (MkDPair s (t, u)) = MkDPair s (rewrite v in t, u)
closureReduces {clos = MkClos (Lam n) env} CLam f = MkDPair (subst sigma (Lam n)) (Refl, MkDPair sigma (f, Refl))
closureReduces {m = l `App` r} (CApp {n} x y) f with (closureReduces {sigma} x f)
  closureReduces {m = l `App` r} (CApp {n = n} x y) f | (MkDPair _ (z, (MkDPair tau (w, v)))) with (v)
    closureReduces {m = l `App` r} (CApp {n = n} x y) f | (MkDPair _ (z, (MkDPair tau (w, v)))) | Refl with (closureReduces {sigma = extSubst tau (subst sigma r)} y (envExt {sigma = tau} {clos = MkClos r env} {n = (subst sigma r)} w (MkDPair sigma (f, Builtin.Refl))))
      closureReduces {m = l `App` r} (CApp {n = n} x y) f | (MkDPair _ (z, (MkDPair tau (w, v)))) | Refl | (MkDPair n' (toN', u)) with (BetaLam {n = subst (exts tau) n} {m = (subst sigma r)})
        closureReduces {m = l `App` r} (CApp {n = n} x y) f | (MkDPair _ (z, (MkDPair tau (w, v)))) | Refl | (MkDPair n' (toN', u)) | betaTauNSigmaR =
          let rs = betaTauNSigmaR `Trans` (rewrite subSub {m = n} {sigma1 = exts tau} {sigma2 = substZero (subst sigma r)} in toN') in
            let g = appLCong z >> rs in MkDPair n' (g, u)


public export
cbnReduce : FunExt
  => {m : Empty |- Star}
  -> {ctx : _}
  -> {env : ClosEnv ctx} 
  -> {n' : ctx :< Star |- Star}
  -> Empty |- (m, MkClos (Lam n') env) -> (n : (Empty :< Star |- Star) ** (m -=>> Lam n))
cbnReduce x with (closureReduces {sigma = ids} x envId)
  cbnReduce x | (MkDPair n (rs, (MkDPair sigma (h, eq2)))) =
    MkDPair (subst (exts sigma) n') (replace {p = \ n => m -=>> n} eq2 (replace {p = \ m => m -=>> n} (subId {m}) rs))
