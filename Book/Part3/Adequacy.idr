module Book.Part3.Adequacy

import Book.Part3.Denotational
import Book.Part3.Soundness
import Book.Part3.Soundness2
import Book.Part2.BigStep
import Book.Part2.Untyped
import Control.Function.FunExt
import Control.Relation

aboveFun : Value -> Type
aboveFun u = (v : Value ** w : Value ** v |~> w :<=: u)

aboveFunLt : {u, u' : _} -> aboveFun u -> u :<=: u' -> aboveFun u'
aboveFunLt (v ** w ** vwcu) lt = (v ** w ** vwcu `Trans` lt)

aboveFunBot : Not (aboveFun Bot)
aboveFunBot (v ** w ** lt) with (subInvFun lt)
  aboveFunBot (v ** w ** lt) | (ctx ** (ctxsubsetbot, f, lt1, lt2)) with (allFuncsElem f)
    aboveFunBot (v ** w ** lt) | (ctx ** (ctxsubsetbot, f, lt1, lt2)) | (v' ** w' ** elem) with (ctxsubsetbot elem)
      aboveFunBot (v ** w ** lt) | (ctx ** (ctxsubsetbot, f, lt1, lt2)) | (v' ** w' ** elem) | isBot impossible

aboveFunU : {u, u' : _} -> aboveFun (u `U` u') -> Either (aboveFun u) (aboveFun u')
aboveFunU (v ** w ** vwcuu') with (subInvFun vwcuu')
  aboveFunU (v ** w ** vwcuu') | (ctx ** (ctxsubsetuu', f, lt1, lt2)) with (allFuncsElem f)
    aboveFunU (v ** w ** vwcuu') | (ctx ** (ctxsubsetuu', f, lt1, lt2)) | (v' ** w' ** elem) with (ctxsubsetuu' elem)
      aboveFunU (v ** w ** vwcuu') | (ctx ** (ctxsubsetuu', f, lt1, lt2)) | (v' ** w' ** elem) | (Left x) = Left (v' ** w' ** elemLt x)
      aboveFunU (v ** w ** vwcuu') | (ctx ** (ctxsubsetuu', f, lt1, lt2)) | (v' ** w' ** elem) | (Right x) = Right (v' ** w' ** elemLt x)

notAboveFunU : {u, u' : _} -> Not (aboveFun u) -> Not (aboveFun u') -> Not (aboveFun (u `U` u'))
notAboveFunU notu notu' aboveFunOfUU' with (aboveFunU aboveFunOfUU')
  notAboveFunU notu notu' aboveFunOfUU' | (Left aboveFunOfU) = notu aboveFunOfU
  notAboveFunU notu notu' aboveFunOfUU' | (Right aboveFunOfU') = notu' aboveFunOfU'

aboveFunInj1 : {u, u' : _} -> aboveFun u -> aboveFun (u `U` u')
aboveFunInj1 (v ** w ** vwcu) = (v ** w ** Inj1 vwcu)

aboveFunInj2 : {u, u' : _} -> aboveFun u' -> aboveFun (u `U` u')
aboveFunInj2 (v ** w ** vwcu') = (v ** w ** Inj2 vwcu')

notAboveFunUInv : {u, u' : _} -> Not (aboveFun (u `U` u')) -> (Not (aboveFun u), Not (aboveFun u'))
notAboveFunUInv f = (f . aboveFunInj1, f . aboveFunInj2)

aboveFunDec : (v : _) -> Dec (aboveFun v)
aboveFunDec Bot = No aboveFunBot
aboveFunDec (x |~> y) = Yes (x ** y ** reflI)
aboveFunDec (x `U` y) with (aboveFunDec x, aboveFunDec y)
  aboveFunDec (x `U` y) | (Yes prf, w) = Yes (aboveFunInj1 prf)
  aboveFunDec (x `U` y) | (No contra, Yes prf) = Yes (aboveFunInj2 prf)
  aboveFunDec (x `U` y) | (No contra, No contra') = No (notAboveFunU contra contra')

V : Value -> Clos -> Type
E : Value -> Clos -> Type

V v (MkClos (Var y) env) = Void
V v (MkClos (y `App` z) env) = Void
V Bot (MkClos (Lam y) env) = ()
V (v |~> w) (MkClos (Lam n) env) = {c : Clos} -> E v c -> aboveFun w
  -> (c' : Clos ** (env :: c |- (n, c'), V w c'))
V (u `U` v) (MkClos (Lam n) env) = (V u (MkClos (Lam n) env), V v (MkClos (Lam n) env))

E v (MkClos m ctx') = (_ : aboveFun v) -> (c : Clos ** (ctx' |- (m, c), V v c))

G : {ctx : _} -> Denotational.Env ctx -> ClosEnv ctx -> Type
G {ctx} env env' = {x : ctx `Has` Star} -> E (env x) (env' x)

GEmpty : G {ctx = Empty} Empty Empty
GEmpty impossible

GExt : {ctx : _} -> {env : Env ctx} -> {env' : ClosEnv ctx} -> {v : _} -> {c : _}
    -> G env env' -> E v c -> G (env :: v) (env' :: c)
GExt g e {x = Z} = e
GExt g e {x = (S x)} = g

data WHNF : {ctx : _} -> {a : LambdaType} -> ctx |- a -> Type where
  IsLam : {ctx : _} -> {n : ctx :: Star |- Star} -> WHNF (Lam n)

VWHNF : {ctx : _} -> {env : ClosEnv ctx} -> {m : ctx |- Star} -> {v : _}
  -> V v (MkClos m env) -> WHNF m
VWHNF {m = (Var y)} x impossible
VWHNF {m = (Lam y)} x = IsLam
VWHNF {m = (y `App` z)} x impossible

VUIntro : {c : _} -> {u,v : _} -> V u c -> V v c -> V (u `U` v) c
VUIntro {c = (MkClos (Var z) f)} _ _ impossible
VUIntro {c = (MkClos (z `App` w) f)} _ _ impossible
VUIntro {c = (MkClos (Lam z) f)} uc vc = (uc, vc)

notAboveFunV : {v : _} -> {ctx : _} -> {env' : ClosEnv ctx} -> {n : ctx :: Star |- Star}
            -> Not (aboveFun v)
            -> V v (MkClos (Lam n) env')
notAboveFunV {v = Bot} af = ()
notAboveFunV {v = (v |~> w)} af = absurd $ af (v ** w ** reflI)
notAboveFunV {v = (v1 `U` v2)} af = (notAboveFunV (af . aboveFunInj1), notAboveFunV (af . aboveFunInj2))

subV : {c : _} -> {v, v' : _} -> V v c -> v' :<=: v -> V v' c
subE : {c : _} -> {v, v' : _} -> E v c -> v' :<=: v -> E v' c
subVLemma
   : {z : (ctx :: Star) |- Star}
  -> {f : (Has ctx Star -> Clos)}
  -> (w1 : Value)
  -> (w2 : Value)
  -> (v : Value)
  -> (vc : (V (v |~> w1) (MkClos (Lam z) f), V (v |~> w2) (MkClos (Lam z) f)))
  -> {c : Clos}
  -> E v c -> aboveFun (w1 `U` w2) -> (c' : Clos ** ((f :: c) |- (z, c'), V (w1 `U` w2) c'))
subVLemma w1 w2 v (vcw1, vcw2) ev sf with (aboveFunDec w1, aboveFunDec w2)
  subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, Yes af2) with (vcw1 ev af1, vcw2 ev af2)
    subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, Yes af2) | ((MkClos m delta ** (mc2, vw1)), (_ ** (mc3, vw2))) with (bigStepDet mc3 mc2)
      subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, Yes af2) | ((MkClos m delta ** (mc2, vw1)), (_ ** (mc3, vw2))) | Refl with (VWHNF vw1)
        subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, Yes af2) | ((MkClos (Lam n) delta ** (mc2, vw1)), (_ ** (mc3, vw2))) | Refl | IsLam
          = (MkClos (Lam n) delta ** (mc2, (vw1, vw2)))
  subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, No naf2) with (vcw1 ev af1)
    subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, No naf2) | ((MkClos m delta) ** (mc2, vw1)) with (VWHNF vw1)
      subVLemma w1 w2 v (vcw1, vcw2) ev sf | (Yes af1, No naf2) | ((MkClos (Lam n) delta) ** (mc2, vw1)) | IsLam
        = (MkClos (Lam n) delta ** (mc2, (vw1, notAboveFunV naf2)))
  subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, Yes af2) with (vcw2 ev af2)
    subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, Yes af2) | ((MkClos m delta) ** (mc3, vw2)) with (VWHNF vw2)
      subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, Yes af2) | ((MkClos (Lam n) delta) ** (mc3, vw2)) | IsLam
        = (MkClos (Lam n) delta ** (mc3, (notAboveFunV naf1, vw2)))
  subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, No naf2) with (aboveFunU sf)
    subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, No naf2) | (Left af1) = absurd $ naf1 af1
    subVLemma w1 w2 v (vcw1, vcw2) ev sf | (No naf1, No naf2) | (Right af2) = absurd $ naf2 af2

subV {c = MkClos (Var z) f} _ _ impossible
subV {c = MkClos (z `App` w) f} _ _ impossible
subV {c = MkClos (Lam z) f} vc Absurd = ()
subV {c = MkClos (Lam z) f} vc (Union x y) = (subV vc x, subV vc y)
subV {c = MkClos (Lam z) f} vc (Inj1 x) = subV (fst vc) x
subV {c = MkClos (Lam z) f} vc (Inj2 x) = subV (snd vc) x
subV {c = MkClos (Lam z) f} vc (x `Trans` y) = subV (subV vc y) x
subV {v = v |~> w} {v' = v' |~> w'} {c = MkClos (Lam z) f} vc (Fun lt1 lt2) = \ ev1, sf =>
  case vc (subE ev1 lt1) (aboveFunLt sf lt2) of
    (c' ** (tcs, vwc)) => (c' ** (tcs, subV vwc lt2))
subV {c = MkClos (Lam z) f} {v = (v |~> w1) `U` (v |~> w2)} vc Dist = subVLemma w1 w2 v vc

subE {c = MkClos m f} ev lt = \ af => case ev (aboveFunLt af lt) of
  (c ** (mc, vv)) => (c ** (mc, subV vv lt))

kthX : {ctx : _} -> {env : ClosEnv ctx} -> {x : ctx `Has` Star}
    -> (ctx' : Context ** env' : ClosEnv ctx' ** m : ctx' |- Star ** env x = MkClos m env')
kthX {env} {x} with (env x)
  kthX {env = env} {x = x} | (MkClos {ctx = ctx'} m env') = (ctx' ** (env' ** (m ** Refl)))


judgeE : {ctx : _} -> {env : Env ctx} -> {closEnv : ClosEnv ctx} -> {m : ctx |- Star} -> {v : _}
      -> G env closEnv -> env |- (m, v) -> E v (MkClos m closEnv)
judgeE gEnvClosEnv (Var {x}) fEnvX with (kthX {env = closEnv} {x}, gEnvClosEnv {x})
  judgeE gEnvClosEnv (Var {x = x}) fEnvX | ((ctx' ** closEnv' ** m' ** eq), gEnvClosEnvX) =
    case replace {p = E (env x)} eq gEnvClosEnv fEnvX of
      (c ** (m'c, vEnvx)) => (c ** (CVar eq m'c, vEnvx))
judgeE gEnvClosEnv (FunElim {m} {v = v1} x y) fEnvX with (judgeE gEnvClosEnv x (v1 ** v ** reflexive))
  judgeE gEnvClosEnv (FunElim x y) fv | (MkClos l' env' ** (ll', vv1v)) with (VWHNF vv1v)
    judgeE gEnvClosEnv (FunElim x y) fv | (MkClos (Lam n) env' ** (ll', vv1v)) | IsLam with (vv1v {c = MkClos m closEnv} (judgeE gEnvClosEnv y) fv)
      judgeE gEnvClosEnv (FunElim x y) fEnvX | (MkClos (Lam n) env' ** (ll', vv1v)) | IsLam | (c' ** (nc', vv)) = (c' ** (CApp ll' nc', vv))
judgeE gEnvClosEnv {v = v |~> w} (FunIntro {n} x) fEnvX = (MkClos (Lam n) closEnv ** (CLam, \evc, fw => judgeE (GExt gEnvClosEnv fw) x))
judgeE gEnvClosEnv BotIntro fEnvX = absurd (aboveFunBot fEnvX)
judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX with (aboveFunDec v1, aboveFunDec v2)
  judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, Yes af2) with (judgeE gEnvClosEnv x af1, judgeE gEnvClosEnv y af2)
    judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, Yes af2) | ((c1 ** (mc1, vv1)), (c2 ** (mc2, vv2))) with (bigStepDet mc1 mc2)
      judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, Yes af2) | ((c1 ** (mc1, vv1)), (c1 ** (mc2, vv2))) | Refl = (c1 ** (mc1, VUIntro vv1 vv2))
  judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, No naf2) with (judgeE gEnvClosEnv x af1)
    judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, No naf2) | (MkClos n f ** (mc, vv1)) with (VWHNF vv1)
      judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (Yes af1, No naf2) | (MkClos (Lam n) f ** (mc, vv1)) | IsLam = (MkClos (Lam n) f ** (mc, VUIntro vv1 (notAboveFunV naf2)))
  judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (No naf1, Yes af2) with (judgeE gEnvClosEnv y af2)
    judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (No naf1, Yes af2) | (MkClos n f ** (mc, vv2)) with (VWHNF vv2)
      judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (No naf1, Yes af2) | (MkClos (Lam n) f ** (mc, vv2)) | IsLam = (MkClos (Lam n) f ** (mc, VUIntro (notAboveFunV naf1) vv2))
  judgeE {v=v1 `U` v2} gEnvClosEnv (UIntro x y) fEnvX | (No naf1, No naf2) = absurd (notAboveFunU naf1 naf2 fEnvX)
judgeE gEnvClosEnv (Sub {v = w} x y) fEnvX with (judgeE gEnvClosEnv x (aboveFunLt fEnvX y))
  judgeE gEnvClosEnv (Sub {v = w} x y) fEnvX | (c ** (mc, vw)) = (c ** (mc, subV vw y))

public export
denoteImpliesJudge : {m : Empty |- Star} -> {n : Empty :: Star |- Star} -> Denote m == Denote (Lam n)
  -> (ctx : _ ** n' : (ctx :: Star |- Star) ** closEnv : ClosEnv ctx ** (Empty |- (m, MkClos (Lam n') closEnv)))
denoteImpliesJudge eq with (judgeE GEmpty ((snd (eq Empty (Bot |~> Bot))) (FunIntro BotIntro)) (Bot ** Bot ** reflexive))
  denoteImpliesJudge eq | (MkClos {ctx} l f ** (lc, vv)) with (VWHNF vv)
    denoteImpliesJudge eq | (MkClos {ctx} (Lam l) f ** (lc, vv)) | IsLam = (ctx ** l ** f ** lc)

adequacy : FunExt => {m : Empty |- Star} -> {n : Empty :: Star |- Star}
        -> Denote m == Denote (Lam n)
        -> (n' : Empty :: Star |- Star ** m -=>> Lam n')
adequacy eq with (denoteImpliesJudge eq)
  adequacy eq | (ctx ** n' ** closEnv ** mJudgment) = cbnReduce mJudgment

reduceCbn : FunExt => {m : Empty |- Star} -> {n : Empty :: Star |- Star}
          -> m -=>> Lam n
          -> (ctx : _ ** n' : ctx :: Star |- Star ** closEnv : ClosEnv ctx ** Empty |- (m, MkClos (Lam n') closEnv))
reduceCbn mToLamN = denoteImpliesJudge (soundness mToLamN)

cbnIffReduce : FunExt => {m : Empty |- Star}
         -> (n : Empty :: Star |- Star ** m -=>> Lam n)
            `iff`
            (ctx : _ ** n' : ctx :: Star |- Star ** closEnv : ClosEnv ctx ** Empty |- (m, MkClos (Lam n') closEnv))
cbnIffReduce = ( \ x => reduceCbn (snd x), \ x => cbnReduce (snd (snd (snd x))) )

