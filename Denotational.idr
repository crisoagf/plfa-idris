module Denotational
import Untyped
import Substitution
import Quantifiers
import Data.Nat
import Data.Vect

data Value = Bot | (|~>) Value Value | U Value Value

infix 4 :<=:
infix 4 :<<=:
infixl 5 `U`
infix 5 `uEnv`
infixr 7 |~>
infixl 5 ::

data (:<=:) : Value -> Value -> Type where
  Absurd : Bot :<=: v
  Union : v :<=: u -> w :<=: u -> v `U` w :<=: u
  Inj1 : u :<=: v -> u :<=: v `U` w
  Inj2 : u :<=: w -> u :<=: v `U` w
  Trans : {v : Value} -> u :<=: v -> v :<=: w -> u :<=: w
  Fun : v' :<=: v -> w :<=: w' -> v |~> w :<=: v' |~> w'
  Dist : v |~> (w `U` w') :<=: (v |~> w) `U` (v |~> w')

umono : v :<=: v' -> w :<=: w' -> (v `U` w) :<=: (v' `U` w')
umono x y = Union (Inj1 x) (Inj2 y)

reflI : {v : Value} -> v :<=: v
reflI {v = Bot} = Absurd
reflI {v = (x |~> y)} = Fun reflI reflI
reflI {v = (x `U` y)} = umono reflI reflI

uFunDist : {v, w, v', w' : _} -> (v `U` v') |~> (w `U` w') :<=: (v |~> w) `U` (v' |~> w')
uFunDist = Dist `Trans` umono (Fun (Inj1 reflI) reflI) (Fun (Inj2 reflI) reflI)

uLtInvL : {u, v, w : _} -> u `U` v :<=: w -> u :<=: w
uLtInvL (Union x y) = x
uLtInvL (Inj1 x) = Inj1 (uLtInvL x)
uLtInvL (Inj2 x) = Inj2 (uLtInvL x)
uLtInvL (x `Trans` y) = uLtInvL x `Trans` y

uLtInvR : {u, v, w : _} -> u `U` v :<=: w -> v :<=: w
uLtInvR (Union x y) = y
uLtInvR (Inj1 x) = Inj1 (uLtInvR x)
uLtInvR (Inj2 x) = Inj2 (uLtInvR x)
uLtInvR (x `Trans` y) = uLtInvR x `Trans` y

Env : (0 _ : Context) -> Type
Env ctx = (x : ctx `Has` Star) -> Value

Empty : Env Empty
Empty x impossible

(::) : Env ctx -> Value -> Env (ctx :: Star)
(::) f y Z = y
(::) f y (S x) = f x

init : Env (ctx :: Star) -> Env ctx
init f x = f (S x)

last : Env (ctx :: Star) -> Value
last f = f Z

initLast : {auto extn : Extensionality} -> (env : Env (ctx :: Star)) -> env = init env :: last env
initLast env = extn lemma
  where lemma : (x : _) -> env x = (init env :: last env) x
        lemma Z = Refl
        lemma (S x) = Refl

(:<<=:) : Env ctx -> Env ctx -> Type
(:<<=:) env env' = (x : ctx `Has` Star) -> env x :<=: env' x

botEnv : Env ctx
botEnv x = Bot

uEnv : Env ctx -> Env ctx -> Env ctx
uEnv f g x = f x `U` g x

reflI' : {env : Env ctx} -> env :<<=: env
reflI' x = reflI {v = env x}

inj1 : (env : Env ctx) -> (env' : Env ctx) -> env :<<=: env `uEnv` env'
inj1 env env' x = Inj1 reflI

inj2 : (env : Env ctx) -> (env' : Env ctx) -> env' :<<=: env `uEnv` env'
inj2 env env' x = Inj2 reflI

data (|-) : Env ctx -> (ctx |- Star, Value) -> Type where
  Var : {x : _} -> env |- (Var x, env x)
  FunElim : env |- (l, v |~> w) -> env |- (m, v) -> env |- (App l m, w)
  FunIntro : {v : _} -> env :: v |- (n, w) -> env |- (Lam n, v |~> w)
  BotIntro : env |- (m, Bot)
  UIntro : env |- (m, v) -> env |- (m, w) -> env |- (m, v `U` w)
  Sub : env |- (m, v) -> w :<=: v -> env |- (m, w)

id : Empty |- Star
id = Lam (Var Z)

denotId1 : env |- (Denotational.id, Bot |~> Bot)
denotId1 = FunIntro Var

denotId2 : env |- (Denotational.id, (Bot |~> Bot) |~> (Bot |~> Bot))
denotId2 = FunIntro Var

denotId3 : env |- (Denotational.id, Bot |~> Bot `U` (Bot |~> Bot) |~> (Bot |~> Bot))
denotId3 = UIntro denotId1 denotId2

idAppId : {env : _} -> {u : _} -> env |- (Denotational.id `App` Denotational.id, u |~> u)
idAppId = FunElim (FunIntro Var) (FunIntro Var)

denotTwoCh : {ctx : _} -> {env : Env ctx} -> {u, v, w : _} -> env |- (Untyped.twoCh, ((u |~> v `U` v |~> w) |~> u |~> w))
denotTwoCh = FunIntro (FunIntro (FunElim (Sub Var (Inj2 reflI)) (FunElim (Sub Var (Inj1 reflI)) Var)))

del : ctx |- Star
del = Lam (Var Z `App` Var Z)

denotDel : {v, w : _} -> env |- (Denotational.del, ((v |~> w) `U` v) |~> w)
denotDel = FunIntro
  (FunElim (Sub Var (Inj1 reflI)) (Sub Var (Inj2 reflI)))

omega : ctx |- Star
omega = del `App` del

denotOmega : Empty |- (Denotational.omega, Bot)
denotOmega = FunElim denotDel (UIntro (FunIntro BotIntro) BotIntro)

denotPlusCh : {ctx : _} -> {0 env : Env ctx} -> {u,v,w,x,k : _} -> env |- (Untyped.plusCh, (v |~> x |~> w) |~> (k |~> u |~> x) |~> (v `U` k) |~> u |~> w)
denotPlusCh = FunIntro . FunIntro . FunIntro . FunIntro $ FunElim (FunElim Var (Sub Var (Inj1 reflI))) (FunElim (FunElim Var (Sub Var (Inj2 reflI))) Var)

iff : Type -> Type -> Type
iff p q = (p -> q, q -> p)

Denotation : Context -> Type
Denotation ctx = (Env ctx -> Value -> Type)

Denote : (m : ctx |- Star) -> Denotation ctx
Denote m env v = env |- (m, v)

(==) : Denotation ctx -> Denotation ctx -> Type
d1 == d2 = (env : Env ctx) -> (v : Value) -> d1 env v `iff` d2 env v

refl : {0 m : Denotation ctx} -> m == m
refl env v = (\x => x, \x => x)

sym : {0 m, n : Denotation ctx} -> m == n -> n == m
sym f env v = let (mn, nm) = f env v in (nm, mn)

trans : {0 m1, m2, m3 : Denotation ctx} -> m1 == m2 -> m2 == m3 -> m1 == m3
trans f g env v with (f env v)
  trans f g env v | (m1m2,m2m1) with (g env v)
    trans f g env v | (m1m2,m2m1) | (m2m3,m3m2) = (m2m3 . m1m2, m2m1 . m3m2)

ext : {0 env : Env ctx} -> {env' : Env ctx'} -> {v : _} -> (rho : Rename ctx ctx')
  -> env :<<=: (env' . rho) -> (env :: v) :<<=: ((env' :: v) . ext rho)
ext rho f Z = reflI
ext rho f (S x) = f x

renamePres : (rho : Rename ctx ctx') -> {env' : _} -> env :<<=: (env' . rho) -> env |- (m, v) -> env' |- (rename rho m, v)
renamePres rho f (Var {x}) = Sub Var (f x)
renamePres rho f (FunElim x y) = FunElim (renamePres rho f x) (renamePres rho f y)
renamePres rho f (FunIntro x) = FunIntro (renamePres (ext rho) (ext rho f) x)
renamePres rho f BotIntro = BotIntro
renamePres rho f (UIntro x y) = UIntro (renamePres rho f x) (renamePres rho f y)
renamePres rho f (Sub x y) = Sub (renamePres rho f x) y

ltEnv : {auto extn : Extensionality}
     -> {env' : _}
     -> env |- (m, v) -> env :<<=: env' -> env' |- (m, v)
ltEnv x f with (renamePres (\ x => x) f x)
  ltEnv x f | c = rewrite sym (renameId {m}) in c

upEnv : {auto extn : Extensionality}
     -> {env : _} -> {u2 : _} -> (env :: u1) |- (m, v) -> u1 :<=: u2 -> (env :: u2) |- (m, v)
upEnv x y = ltEnv x (extLe y)
  where extLe : u1 :<=: u2 -> (env :: u1) :<<=: (env :: u2)
        extLe y Z = y
        extLe y (S x) = reflI

dsuc : Vect (S n) Value -> Value
dsuc (a :: []) = Bot
dsuc (ask :: (ak :: ls)) = ak |~> ask `U` dsuc (ak :: ls)

vecLast : Vect (S n) Value -> Value
vecLast (a :: []) = a
vecLast (a :: (b :: bs)) = vecLast (b :: bs)

dCh : Vect (S n) Value -> Value
dCh (an :: ls) = dsuc (an :: ls) |~> vecLast (an :: ls) |~> an

applyN : (n : Nat) -> Empty :: Star :: Star |- Star
applyN 0 = var 0
applyN (S n) = var 1 `App` applyN n

church : (n : Nat) -> Empty |- Star
church n = Lam (Lam (applyN n))

denotApplyN
  : {auto extn : Extensionality}
  -> (x : Value) -> (xs : Vect n Value) -> ((Empty :: dsuc (x :: xs)) :: vecLast (x :: xs)) |- (applyN n, x)
denotApplyN x [] = Var
denotApplyN x (y :: xs) with (denotApplyN y xs)
  denotApplyN x (y :: xs) | denotTail = FunElim (Sub Var (Inj1 reflI)) (ltEnv denotTail lemma)
    where lemma : (Empty :: dsuc (y :: xs) :: vecLast (y :: xs)) :<<=: (Empty :: ((y |~> x) `U` dsuc (y :: xs)) :: vecLast (y :: xs))
          lemma Z = reflI
          lemma (S Z) = Inj2 reflI

denotChurch
  : {auto extn : Extensionality}
  -> (ls : Vect (S n) Value) -> Empty |- (church n, dCh ls)
denotChurch (x :: xs) = FunIntro . FunIntro $ denotApplyN x xs

infix 5 `Elem`
infix 5 `Subset`

Elem : Value -> Value -> Type
Elem x Bot = x = Bot
Elem x (y |~> z) = x = y |~> z
Elem x (y `U` z) = Either (Elem x y) (Elem x z)

Subset : Value -> Value -> Type
Subset x y = {u : _} -> u `Elem` x -> u `Elem` y

elemLt : {x, y: Value} -> Elem x y -> x :<=: y
elemLt {x = Bot} {y = Bot} Refl = Absurd
elemLt {x = (_ |~> _)} {y = (y |~> w)} Refl = reflI
elemLt {x = x} {y = (y `U` w)} (Left z) = Inj1 (elemLt z)
elemLt {x = x} {y = (y `U` w)} (Right z) = Inj2 (elemLt z)

subsetLt : {x,y : Value} -> x `Subset` y -> x :<=: y
subsetLt {x = Bot} {y = y} f = Absurd
subsetLt {x = (x |~> z)} {y = y} f with (f {u = _ |~> _} Refl)
  subsetLt {x = (x |~> z)} {y = y} f | with_pat = elemLt with_pat
subsetLt {x = (x `U` z)} {y = y} f = Union (subsetLt \ t => f (Left t)) (subsetLt \ t => f (Right t))

uSubsetInv : (u `U` v) `Subset` w -> (u `Subset` w, v `Subset` w)
uSubsetInv f = (f . Left, f . Right)

arrSubsetElem : {v,w : _} -> v |~> w `Subset` u -> v |~> w `Elem` u
arrSubsetElem f = f Refl

data Func : Value -> Type where
  MkFunc : {v, w: Value} -> Func (v |~> w)

mkFunc : {u,v,w : _} -> u = v |~> w -> Func u
mkFunc Refl = MkFunc

elimFunc : Func u -> (v ** w ** u = v |~> w)
elimFunc (MkFunc {v} {w}) = (v ** w ** Refl)

allFuncs : Value -> Type
allFuncs v = {u : _} -> u `Elem` v -> Func u

notFuncBot : Not (Func Bot)
notFuncBot MkFunc impossible

allFuncsElem : {u : _} -> allFuncs u -> (v ** w ** v |~> w `Elem` u)
allFuncsElem {u = Bot} f = absurd (notFuncBot (f Refl))
allFuncsElem {u = (x |~> y)} f = MkDPair x (MkDPair y Refl)
allFuncsElem {u = (x `U` y)} f with (allFuncsElem {u = x} (f . Left))
  allFuncsElem {u = (x `U` y)} f | (MkDPair fst (MkDPair z snd)) = (fst ** z ** Left snd)

domain : (u : Value) -> Value
domain Bot = Bot
domain (x |~> y) = x
domain (x `U` y) = domain x `U` domain y

codomain : (u : Value) -> Value
codomain Bot = Bot
codomain (x |~> y) = y
codomain (x `U` y) = codomain x `U` codomain y

domainContains : {u, v, w : _} -> (v |~> w) `Elem` u -> v `Subset` domain u
domainContains {u = Bot} x y = case x of {}
domainContains {u = (z |~> s)} Refl y = y
domainContains {u = (z `U` s)} (Left x) y = Left (domainContains x y)
domainContains {u = (z `U` s)} (Right x) y = Right (domainContains x y)

containsCodomain : {u, v, w : _} -> u `Subset` v |~> w -> codomain u `Subset` w
containsCodomain {u = Bot} f Refl = case f Refl of {}
containsCodomain {u = (y |~> z)} f x with (f Refl)
  containsCodomain {u = (v |~> w)} f x | Refl = x
containsCodomain {u = (y `U` z)} f (Left x) = containsCodomain (f . Left) x
containsCodomain {u = (y `U` z)} f (Right x) = containsCodomain (f . Right) x

factor : (u, u', v, w : Value) -> Type
factor u u' v w = (u' `Subset` u, allFuncs u', domain u' :<=: v, w :<=: codomain u')

subInvTrans : {u', u2, u : Value} -> allFuncs u' -> u' `Subset` u -> ({v', w' : Value} -> v' |~> w' `Elem` u -> (u3 : Value ** factor u2 u3 v' w')) -> (u3 : Value ** factor u2 u3 (domain u') (codomain u'))
subInvTrans {u' = Bot} {u2 = u2} {u = u} f g ih = absurd (notFuncBot (f Refl))
subInvTrans {u' = (x |~> y)} {u2 = u2} {u = u} f g ih = ih (g Refl)
subInvTrans {u' = (u1' `U` u2')} {u2 = u2} {u = u} f g ih with (uSubsetInv g)
  subInvTrans {u' = (u1' `U` u2')} {u2 = u2} {u = u} f g ih | (u1cu, u2cu) = case subInvTrans {u' = u1'} {u2} {u} (\ z => f (Left z)) u1cu ih of
    (u31 ** (u31cu2, fu31, du31cdu1', cu1'ccu31)) => case subInvTrans {u' = u2'} {u2} {u} (\ z => f (Right z)) u2cu ih of
      (u32 ** (u32cu2, fu32, du32cdu2', cu1'ccu32)) => (u31 `U` u32 ** (either u31cu2 u32cu2, either fu31 fu32, umono du31cdu1' du32cdu2', umono cu1'ccu31 cu1'ccu32))

subInv : {u1, u2 : Value} -> u1 :<=: u2 -> {v, w : Value} -> v |~> w `Elem` u1 -> (u3 : Value ** factor u2 u3 v w)
subInv {u1 = Bot} {u2 = u2} Absurd {v = v} {w = w} y impossible
subInv {u1 = u11 `U` u12} {u2 = u2} (Union x z) {v = v} {w = w} (Left y) = subInv x y
subInv {u1 = u11 `U` u12} {u2 = u2} (Union x z) {v = v} {w = w} (Right y) = subInv z y
subInv {u1 = u1} {u2 = (u21 `U` u22)} (Inj1 x) {v = v} {w = w} y with (subInv x y)
  subInv {u1 = u1} {u2 = (u21 `U` u22)} (Inj1 x) {v = v} {w = w} y | (u31 ** (u31cu21, fu31, domu31cv, wccodu31))
    = (u31 ** (\ z => Left (u31cu21 z), fu31, domu31cv, wccodu31))
subInv {u1 = u1} {u2 = (u21 `U` u22)} (Inj2 x) {v = v} {w = w} y with (subInv x y)
  subInv {u1 = u1} {u2 = (u21 `U` u22)} (Inj2 x) {v = v} {w = w} y | (u32 ** (u32cu22, fu32, domu32cv, wccodu32))
    = (u32 ** (\ z => Right (u32cu22 z), fu32, domu32cv, wccodu32))
subInv {u1 = u1} {u2 = u2} (x `Trans` z) {v = v} {w = w} y with (subInv x y)
  subInv {u1 = u1} {u2 = u2} (x `Trans` z) {v = v} {w = w} y | (u' **  (u'cu1, fu', domu'cv, wccodu')) with (subInvTrans fu' u'cu1 (subInv z))
    subInv {u1 = u1} {u2 = u2} (x `Trans` z) {v = v} {w = w} y | (u' **  (u'cu1, fu', domu'cv, wccodu')) | (u3 ** (u3cu2, fu3, domu3cdomu', codu'ccodu3))
      = (u3 ** (u3cu2, fu3, domu3cdomu' `Trans` domu'cv, wccodu' `Trans` codu'ccodu3))
subInv {u1 = (u11 |~> u12)} {u2 = (u21 |~> u22)} (Fun x z) {v = u11} {w = u12} Refl = (u21 |~> u22 ** (id, \ Refl => MkFunc, x, z))
subInv {u1 = (v1 |~> (w1 `U` w1'))} {u2 = ((v1 |~> w1) `U` (v1 |~> w1'))} Dist {v = v} {w = w} y with (y)
  subInv {u1 = (v1 |~> (w1 `U` w1'))} {u2 = ((v1 |~> w1) `U` (v1 |~> w1'))} Dist {v = v1} {w = (w1 `U` w1')} y | Refl
    = ((v1 |~> w1 `U` v1 |~> w1') ** (id, triviality, Union reflI reflI, reflI))
  where
    triviality : Either (u = v1 |~> w1) (u = v1 |~> w1') -> Func u
    triviality (Left Refl) = MkFunc
    triviality (Right Refl) = MkFunc

