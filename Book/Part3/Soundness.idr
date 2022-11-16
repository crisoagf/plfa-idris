module Book.Part3.Soundness

import Book.Part3.Compositional
import Book.Part3.Denotational
import Book.Part2.Untyped
import Book.Appendix.Substitution
import Control.Function.FunExt

(|-) : {ctx, ctx' : _} -> Env ctx' -> (Subst ctx ctx', Env ctx) -> Type
(|-) {ctx} env' (sub, env) = ((x : ctx `Has` Star) -> env' |- (sub x, env x))

substExt : {v : _} -> {env : Env ctx} -> {env' : Env ctx'} -> (sub : Subst ctx ctx')
  -> env' |- (sub, env)
  -> (env' :: v) |- (exts sub, env :: v)
substExt sub d Z = Var
substExt sub d (S x) = renamePres S (\ _ => reflI) (d x)

substPres : {v : _} -> {env : Env ctx} -> {env' : Env ctx'} -> {m : ctx |- Star}
  -> (sub : Subst ctx ctx')
  -> env' |- (sub, env)
  -> env |- (m, v)
  -> env' |- (subst sub m, v)
substPres sub s (Var {x}) = s x
substPres sub s (FunElim x y) = FunElim (substPres sub s x) (substPres sub s y)
substPres sub s (FunIntro x) = FunIntro (substPres (exts sub) (substExt sub s) x)
substPres sub s BotIntro = BotIntro
substPres sub s (UIntro x y) = UIntro (substPres sub s x) (substPres sub s y)
substPres sub s (Sub x y) = Sub (substPres sub s x) y

substitution : {v, w : _} -> {env : Env ctx} -> {m : _} -> {n : ctx :: Star |- Star}
  -> (env :: v) |- (n, w)
  -> env |- (m, v)
  -> env |- (replace n m, w)
substitution {m} {v} x y = substPres (substZero m) subZOk x
  where
    subZOk : env |- (substZero m, env :: v)
    subZOk Z = y
    subZOk (S x) = Var

public export
preserve : FunExt => {v : _} -> {env : Env ctx} -> {m : _} -> {n : ctx |- Star}
  -> env |- (m, v)
  -> m -=> n
  -> env |- (n, v)
preserve Var y impossible
preserve (FunElim x z) (IntroAppLeft y) = FunElim (preserve x y) z
preserve (FunElim x z) (IntroAppRight y) = FunElim x (preserve z y)
preserve (FunElim x z) BetaLam = substitution (lambdaInversion x) z
preserve (FunIntro x) (IntroLam y) = FunIntro (preserve x y)
preserve BotIntro y = BotIntro
preserve (UIntro x z) y = UIntro (preserve x y) (preserve z y)
preserve (Sub x z) y = Sub (preserve x y) z

extLt : {v : _} -> {env : Env ctx} -> {env' : Env ctx'}
  -> (rho : Rename ctx ctx')
  -> (env' . rho) :<<=: env
  -> ((env' :: v) . ext rho) :<<=: (env :: v)
extLt rho f Z = reflI
extLt rho f (S x) = f x

renameReflect : {v : _} -> {env : Env ctx} -> {env' : Env ctx'} -> {m : ctx |- Star}
  -> {rho : Rename ctx ctx'}
  -> (env' . rho) :<<=: env
  -> env' |- (rename rho m, v)
  -> env  |- (m, v)
renameReflect {m = (Var y)} alln d with (varInv d)
  renameReflect {m = (Var y)} alln d | lt = Sub Var (lt `Trans` alln y)
renameReflect {m = (Lam y)} alln (FunIntro x) = FunIntro (renameReflect (extLt rho alln) x)
renameReflect {m = (Lam y)} alln BotIntro = BotIntro
renameReflect {m = (Lam y)} alln (UIntro x z) = UIntro (renameReflect alln x) (renameReflect alln z)
renameReflect {m = (Lam y)} alln (Sub x z) = Sub (renameReflect alln x) z
renameReflect {m = (y `App` z)} alln (FunElim x w) = FunElim (renameReflect alln x) (renameReflect alln w)
renameReflect {m = (y `App` z)} alln BotIntro = BotIntro
renameReflect {m = (y `App` z)} alln (UIntro x w) = UIntro (renameReflect alln x) (renameReflect alln w)
renameReflect {m = (y `App` z)} alln (Sub x w) = Sub (renameReflect alln x) w

renameIncReflect : {v',v : _} -> {env : Env ctx} -> {m : _}
  -> (env :: v') |- (rename S m, v)
  -> env |- (m, v)
renameIncReflect x = renameReflect reflI' x

(==) : (x,y : ctx `Has` Star) -> Dec (x = y)
(==) Z Z = Yes Refl
(==) Z (S x) = No (\x => case x of {})
(==) (S x) Z = No (\x => case x of {})
(==) (S x) (S y) with (x == y)
  (==) (S x) (S x) | (Yes Refl) = Yes Refl
  (==) (S x) (S y) | (No contra) = No (\ Refl => contra Refl)

refl : (x : _) -> x == x = Yes Refl
refl Z = Refl
refl (S x) = rewrite refl x in Refl

constEnv : (x : ctx `Has` Star) -> Value -> Env ctx
constEnv x v y with (x == y)
  constEnv x v y | (Yes prf) = v
  constEnv x v y | (No contra) = Bot

sameConstEnv : {x : _} -> (constEnv x v) x = v
sameConstEnv {x} = rewrite refl x in Refl

diffConstEnv : {x, y : _} -> {v : _} -> Not (x = y) -> constEnv x v y = Bot
diffConstEnv neq with (x == y)
  diffConstEnv neq | (Yes prf) = absurd (neq prf)
  diffConstEnv neq | (No contra) = Refl

substReflectVar : {v : _} -> {env' : Env ctx'} -> {x : ctx `Has` Star}
  -> {sigma : Subst ctx ctx'}
  -> env' |- (sigma x, v)
  -> (env : Env ctx ** (env' |- (sigma, env), env |- (Var x, v)))
substReflectVar xv = rewrite sym (sameConstEnv {x} {v}) in
  (constEnv x v ** (constEnvOk, Var))
  where
    constEnvOk : env' |- (sigma, constEnv x v)
    constEnvOk y with (x == y)
      constEnvOk y | (Yes prf) = rewrite sym prf in xv
      constEnvOk y | (No contra) = BotIntro

substBot : {env' : Env ctx'} -> {sigma : Subst ctx ctx'}
  -> env' |- (sigma, Denotational.botEnv)
substBot x = BotIntro

substU : {env' : Env ctx'} -> {env1, env2 : Env ctx} -> {sigma : Subst ctx ctx'}
  -> env' |- (sigma, env1)
  -> env' |- (sigma, env2)
  -> env' |- (sigma, env1 `uEnv` env2)
substU f g x = UIntro (f x) (g x)

lambdaInj : {m, n : ctx :: Star |- Star} -> Lam m = Lam n -> m = n
lambdaInj Refl = Refl

split : FunExt => {m : ctx :: Star |- Star} -> {env' : Env (ctx :: Star)} -> {v : _}
  -> env' |- (m, v)
  -> (init env' :: last env') |- (m, v)
split x = rewrite sym (initLast env') in x

substReflect : FunExt => {env' : Env ctx'} -> {m : ctx |- Star} -> {v : _}
  -> {l : ctx' |- Star} -> {sigma : Subst ctx ctx'}
  -> env' |- (l, v)
  -> subst sigma m = l
  -> (env : Env ctx ** (env' |- (sigma, env), env |- (m, v)))
substReflect {m = Var y} (Var {x}) prf with (Var {env = env'} {x})
  substReflect {m = Var y} (Var {x}) prf | vx = substReflectVar {sigma} (rewrite prf in vx)
substReflect {m = Lam y} (Var {x}) prf impossible
substReflect {m = y `App` z} (Var {x}) prf impossible
substReflect {m = (Var z)} (FunElim x y) prf = substReflectVar {sigma} (rewrite prf in FunElim x y)
substReflect {m = (Lam z)} (FunElim x y) prf impossible
substReflect {m = (z `App` w)} (FunElim x y) Refl with (substReflect x Refl, substReflect y Refl)
  substReflect {m = (z `App` w)} (FunElim x y) Refl | ((env1 ** (s1, m1)), (env2 ** (s2, m2)))
    = (env1 `uEnv` env2 ** (substU {sigma} s1 s2, FunElim (ltEnv m1 (inj1 env1 env2)) (ltEnv m2 (inj2 env1 env2))))
substReflect {m = (Var y)} (FunIntro x) prf = substReflectVar {sigma} (rewrite prf in FunIntro x)
substReflect {m = (Lam y)} (FunIntro x) Refl with (substReflect {sigma = exts sigma} x Refl)
  substReflect {m = (Lam y)} (FunIntro x) Refl | (env ** (z, w)) = (init env ** ((\ x => renameIncReflect (z (S x))), FunIntro (upEnv (split w) (varInv (z Z)))))
substReflect {m = (y `App` z)} (FunIntro x) prf impossible
substReflect {m = m} BotIntro Refl = (botEnv ** (\x => BotIntro, BotIntro))
substReflect {m = m} (UIntro x y) prf with (substReflect x prf, substReflect y prf)
  substReflect {m = m} (UIntro x y) prf | ((env1 ** (s1, m1)), (env2 ** (s2, m2))) = (env1 `uEnv` env2 ** (substU {sigma} s1 s2, UIntro (ltEnv m1 (inj1 env1 env2)) (ltEnv m2 (inj2 env1 env2))))
substReflect {m = m} (Sub x y) prf with (substReflect x prf)
  substReflect {m = m} (Sub x y) prf | (env ** (s, m')) = (env ** (s, Sub m' y))

substZeroReflect : {env : Env ctx} -> {env' : Env (ctx :: Star)} -> {m : ctx |- Star}
  -> env |- (substZero m, env')
  -> (env' :<<=: (env :: last env'), env |- (m, last env'))
substZeroReflect f = (lemma, f Z)
  where
    lemma : env' :<<=: (env :: last env')
    lemma Z = reflI
    lemma (S x) = varInv (f (S x))

substitutionReflect : FunExt => {env : Env ctx} -> {n : ctx :: Star |- Star} -> {m : ctx |- Star} -> {v : _}
  -> env |- (replace n m, v)
  -> (w : Value ** (env |- (m, w), (env :: w) |- (n, v)))
substitutionReflect x with (substReflect x Refl)
  substitutionReflect x | (env' ** (envsigmaenv', env'v)) with (substZeroReflect envsigmaenv')
    substitutionReflect x | (env' ** (envsigmaenv', env'v)) | (lt, envmlastenv')
      = (last env' ** (envmlastenv', ltEnv env'v lt))

public export
reflectBeta : FunExt => {env : Env ctx} -> {m : _} -> {n : _} -> {v : _}
  -> env |- (replace n m, v)
  -> env |- (Lam n `App` m, v)
reflectBeta x with (substitutionReflect x)
  reflectBeta x | (v2' ** (d1', d2')) = FunElim (FunIntro d2') d1'

