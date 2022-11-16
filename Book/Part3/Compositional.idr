module Book.Part3.Compositional

import Book.Part2.Untyped
import Book.Part3.Denotational
import Control.Function.FunExt
import Syntax.PreorderReasoning.Generic
import Syntax.TransitiveReasoning

F : Denotation (ctx :: Star) -> Denotation ctx
F d x Bot = ()
F d x (y |~> z) = d (x :: y) z
F d x (y `U` z) = (F d x y, F d x z)

subF : FunExt => {env : _} -> {v : _} -> {u : _} -> {n : (ctx :: Star) |- Star}
  -> F {ctx} (Denote n) env v -> u :<=: v -> F {ctx} (Denote n) env u
subF d Absurd = ()
subF d (Union lt1 lt2) = (subF d lt1, subF d lt2)
subF (d1, d2) (Inj1 y) = subF d1 y
subF (d1, d2) (Inj2 y) = subF d2 y
subF d (Fun lt lt') = Sub (upEnv d lt) lt'
subF (d1, d2) Dist = UIntro d1 d2
subF d (y `Trans` z) = subF (subF d z) y

denoteLamToFDenote : FunExt => {env : _} -> {v : _} -> {n : (ctx :: Star) |- Star}
  -> Denote (Lam n) env v
  -> F {ctx} (Denote n) env v
denoteLamToFDenote (FunIntro x) = x
denoteLamToFDenote BotIntro = ()
denoteLamToFDenote (UIntro x y) = (denoteLamToFDenote x, denoteLamToFDenote y)
denoteLamToFDenote (Sub d lt) = subF (denoteLamToFDenote d) lt

public export
lambdaInversion : FunExt => {env : Env ctx} -> {n : (ctx :: Star) |- Star}
  -> {v1 : _} -> {v2 : _}
  -> env |- (Lam n, v1 |~> v2) -> (env :: v1) |- (n, v2)
lambdaInversion d = denoteLamToFDenote {v = v1 |~> v2} d

fDenoteToDenoteLam : {env : _} -> {v : _}
  -> {n : (ctx :: Star) |- Star}
  -> F {ctx} (Denote n) env v -> Denote (Lam n) env v
fDenoteToDenoteLam {v = Bot} d = BotIntro
fDenoteToDenoteLam {v = (y |~> z)} d = FunIntro d
fDenoteToDenoteLam {v = (y `U` z)} (d1, d2) = UIntro (fDenoteToDenoteLam d1) (fDenoteToDenoteLam d2)

lamEquiv : FunExt => {ctx : _} -> {n : (ctx :: Star) |- Star} -> Denote (Lam n) == F (Denote n)
lamEquiv env v = (denoteLamToFDenote, fDenoteToDenoteLam)

App : {ctx : _} -> Denotation ctx -> Denotation ctx -> Denotation ctx
App d1 d2 env w = Either (w :<=: Bot) (v : Value ** (d1 env (v |~> w), d2 env v))

appHomo : {env : _} -> {l, m : ctx |- Star} -> {v : _}
  -> Denote (l `App` m) env v -> (Denote l `App` Denote m) env v
appHomo (FunElim {v = v'} x y) = Right (v' ** (x, y))
appHomo BotIntro = Left Absurd
appHomo (UIntro x y) with (appHomo x)
  appHomo (UIntro x y) | (Left z) with (appHomo y)
    appHomo (UIntro x y) | (Left z) | (Left w) = Left (Union z w)
    appHomo (UIntro x y) | (Left z) | (Right (v' ** (w, s)))
      = Right (v' ** (Sub w (Fun reflI (Union (Trans z Absurd) reflI)), s))
  appHomo (UIntro x y) | (Right (v' ** (z, w))) with (appHomo y)
    appHomo (UIntro x y) | (Right (v' ** (w, s))) | (Left z)
      = Right (v' ** (Sub w (Fun reflI (Union reflI (Trans z Absurd))), s))
    appHomo (UIntro x y) | (Right (v' ** (z, w))) | (Right (v'' ** (z', w'))) 
      = Right (v' `U` v'' ** (Sub (UIntro z z') uFunDist, UIntro w w'))
appHomo (Sub d lt) with (appHomo d)
  appHomo (Sub d lt) | (Left x) = Left (lt `Trans` x)
  appHomo (Sub d lt) | (Right (v' ** (x, y))) = Right (v' ** (Sub x (Fun reflI lt), y))

appHomoInv :  {env : _} -> {l, m : ctx |- Star} -> {v : _}
  -> (Denote l `App` Denote m) env v -> Denote (l `App` m) env v
appHomoInv (Left x) = Sub BotIntro x
appHomoInv (Right (v ** (x, y))) = FunElim x y

appEquiv : {l, m : ctx |- Star}
  -> Denote (l `App` m) == Denote l `App` Denote m
appEquiv env v = (appHomo, appHomoInv)

public export
varInv : {env : _} -> Denote (Var x) env v -> v :<=: env x
varInv Var = reflI
varInv BotIntro = Absurd
varInv (UIntro y z) = Union (varInv y) (varInv z)
varInv (Sub y z) = z `Trans` varInv y

varEquiv : {x : _} -> Denote (Var x) == (\ env, v => v :<=: env x)
varEquiv env v = (varInv, \ lt => Sub Var lt)

fCong : d == d' -> F d == F d'
fCong f env v = (\ x => fEq x f, \ x => fEq x (sym f))
  where
    fEq : {env' : _} -> {v' : _} -> F d1 env' v' -> d1 == d2 -> F d2 env' v'
    fEq {v' = Bot} () dd' = ()
    fEq {env'} {v' = (y |~> z)} fd dd' = fst (dd' (env' :: y) z) fd
    fEq {v' = (y `U` z)} fd dd' = (fEq (fst fd) dd', fEq (snd fd) dd')

lamCong : FunExt => {ctx : _} -> {n, n' : ctx :: _ |- _} -> Denote n == Denote n'
  -> Denote (Lam n) == Denote (Lam n')
lamCong nn' = ExplicitCalc {leq = (==)} trans $
  |~ Denote (Lam n)
  <~ F (Denote n ) ...(lamEquiv)
  <~ F (Denote n') ...(fCong nn')
  <~ Denote (Lam n') ...(sym lamEquiv)

AppCong : {ctx : _} -> {d1,d1',d2,d2' : Denotation ctx} -> d1 == d1' -> d2 == d2' -> d1 `App` d2 == d1' `App` d2'
AppCong f g env v = (\ x => appEq x f g, \ x => appEq x (sym f) (sym g))
  where
    appEq : {env' : _} -> {v' : _} -> (d'1 `App` d'2) env' v' -> d'1 == d'1' -> d'2 == d'2' -> (d'1' `App` d'2') env' v'
    appEq (Left x) f g = Left x
    appEq {env' = env'} {v' = v'} (Right (w ** (dwv', dw))) eq1 eq2
      = Right (w ** (fst (eq1 env' (w |~> v')) dwv', fst (eq2 env' w) dw))

appCong : {ctx : _} -> {l, l', m, m' : ctx |- Star} -> Denote l == Denote l' -> Denote m == Denote m' -> Denote (l `App` m) == Denote (l' `App` m')
appCong f g = ExplicitCalc {leq = (==)} trans $
  |~ Denote (l `App` m)
  <~ Denote l `App` Denote m ...(appEquiv)
  <~ Denote l' `App` Denote m' ...(AppCong f g)
  <~ Denote (l' `App` m') ...(sym appEquiv)

data Ctx : Context -> Context -> Type where
  Hole : {ctx : _} -> Ctx ctx ctx
  Lam : {ctx, ctx' : _} -> Ctx (ctx :: Star) (ctx' :: Star) -> Ctx (ctx :: Star) ctx'
  AppL : {ctx, ctx' : _} -> Ctx ctx ctx' -> ctx' |- Star -> Ctx ctx ctx' 
  AppR : {ctx, ctx' : _} -> ctx' |- Star -> Ctx ctx ctx' -> Ctx ctx ctx' 

plug : {0 ctx, ctx' : _} -> Ctx ctx ctx' -> ctx |- Star -> ctx' |- Star
plug Hole y = y
plug (Lam x) y = Lam (plug x y)
plug (AppL x z) y = plug x y `App` z
plug (AppR x z) y = x `App` plug z y

compositionality : FunExt => {ctx, ctx' : _} -> {c : Ctx ctx ctx'} -> {m, n : ctx |- Star}
  -> Denote m == Denote n
  -> Denote (plug c m) == Denote (plug c n)
compositionality {c = Hole} f = f
compositionality {c = (Lam x)} f = lamCong (compositionality f)
compositionality {c = (AppL x y)} f =
    appCong (compositionality {c = x} f) (\ env', v => (\ x => x, \ x => x))
compositionality {c = (AppR x y)} f =
    appCong (\ env', v => (\ x => x, \ x => x)) (compositionality {c = y} f)

Interpret : {ctx : _} -> (m : ctx |- Star) -> Denotation ctx
Interpret (Var y) env v = v :<=: env y
Interpret (Lam y) env v = F (Interpret y) env v
Interpret (y `App` z) env v = (Interpret y `App` Interpret z) env v

denoteInterpret : FunExt => {ctx : _} -> {m : ctx |- Star} -> Denote m == Interpret m
denoteInterpret {m = (Var x)} = varEquiv
denoteInterpret {m = (Lam x)} = ExplicitCalc {leq = (==)} trans $
  |~ Denote (Lam x)
  <~ F (Denote x) ...(lamEquiv)
  <~ F (Interpret x) ...(fCong (denoteInterpret {m = x}))
  <~ Interpret (Lam x) ...(refl)
denoteInterpret {m = (x `App` y)} = ExplicitCalc {leq = (==)} trans $
  |~ Denote (x `App` y)
  <~ Denote x `App` Denote y ...(appEquiv)
  <~ Interpret x `App` Interpret y ...(AppCong (denoteInterpret {m = x}) (denoteInterpret {m = y}))
  <~ Interpret (x `App` y) ...(refl)

