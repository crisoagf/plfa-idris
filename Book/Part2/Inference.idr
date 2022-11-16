module Book.Part2.Inference

import Decidable.Equality
import Book.Part2.MoreMul
%default total

Extensionality : Type
Extensionality = {a : Type} -> {b : a -> Type} -> {f, f' : (x : a) -> b x} -> ((x : a) -> f x = f' x) -> f = f'

Id : Type
Id = String

infix 4 |-
infix 4 |=
infix 5 :::
infixl 5 ::
infixl 6 :!
infixl 7 `App`

data Context : Type where
  Empty : Context
  (::) : Inference.Context -> (Id, LambdaType) -> Context

data TermS : Type
data TermI : Type

data TermS : Type where
  Var : Id -> TermS
  App : TermS -> TermI -> TermS
  Pair : TermS -> TermS -> TermS
  (:!) : TermI -> LambdaType -> TermS

data TermI : Type where
  Lam : Id -> TermI -> TermI
  Zero : TermI
  Suc : TermI -> TermI
  Case : TermS -> TermI -> Id -> TermI -> TermI
  Mu : Id -> TermI -> TermI
  Proj1 : TermS -> TermI
  Proj2 : TermS -> TermI
  CaseP : TermS -> Id -> Id -> TermI -> TermI
  Infer : TermS -> TermI

two : TermI
two = Suc (Suc Zero)

plus : TermI
plus = Mu "p" (Lam "m" (Lam "n" (Case (Var "m")
  (Infer (Var "n"))
  "m" (Suc (Infer $ Var "p" `App` Infer (Var "m") `App` Infer (Var "n"))))))

twoPlusTwo : TermS
twoPlusTwo = (plus :! Nat ~> Nat ~> Nat) `App` two `App` two

chTwo : TermI
chTwo = Lam "s" $ Lam "z" $ Infer $ Var "s" `App` Infer (Var "s" `App` (Infer $ Var "z"))

chPlus : TermI
chPlus = Lam "m" $ Lam "n" $ Lam "s" $ Lam "z" $
  Infer $ Var "m"
    `App` Infer (Var "s")
    `App` Infer (Var "n"
      `App` Infer (Var "s")
      `App` Infer (Var "z"))

suc : TermI
suc = Lam "x" (Suc (Infer (Var "x")))

twoPlusTwoCh : TermS
twoPlusTwoCh = (chPlus :! Ch Nat ~> Ch Nat ~> Ch Nat) `App` chTwo `App` chTwo

twoPlusTwoCh' : {a : LambdaType} -> TermS
twoPlusTwoCh' = (chPlus :! Ch a ~> Ch a ~> Ch a) `App` chTwo `App` chTwo

data Has : Inference.Context -> (Id, LambdaType) -> Type where
  Z : ctx :: (x, a) `Has` (x, a)
  S : Not (x = y) -> ctx `Has` (x, a) -> ctx :: (y, b) `Has` (x, a)

record TypeQ a where
  constructor (:::)
  term : a
  type : LambdaType

mutual
  data (|-) : Inference.Context -> TypeQ TermS -> Type where
    JudgeVar : ctx `Has` (x,a) -> ctx |- (Var x ::: a)
    JudgeApp : {a, b : _} -> ctx |- l ::: a ~> b -> ctx |= m ::: a -> ctx |- App l m ::: b
    JudgePair : ctx |- x ::: a -> ctx |- y ::: b -> ctx |- Pair x y ::: a * b
    JudgeAssert : ctx |= l ::: a -> ctx |- l :! a ::: a
  
  data (|=) : Inference.Context -> TypeQ TermI -> Type where
    JudgeLam : ctx :: (x,a) |= n ::: b -> ctx |= Lam x n ::: a ~> b
    JudgeZero : ctx |= Zero ::: Nat
    JudgeSuc : ctx |= m ::: Nat -> ctx |= Suc m ::: Nat
    JudgeCase : ctx |- l ::: Nat -> ctx |= m ::: a -> ctx :: (x, Nat) |= n ::: a
             -> ctx |= Case l m x n ::: a
    JudgeMu : ctx :: (x, a) |= n ::: a -> ctx |= Mu x n ::: a
    JudgeProj1 : {a,b : _} -> ctx |- l ::: a * b -> ctx |= Proj1 l ::: a
    JudgeProj2 : {a,b : _} -> ctx |- l ::: a * b -> ctx |= Proj2 l ::: b
    JudgeCaseP : {a,b : _} -> ctx |- l ::: a * b -> ctx :: (x, a) :: (y, b) |= m ::: c -> ctx |= CaseP l x y m ::: c
    JudgeInfer : ctx |- m ::: a -> a = b -> ctx |= Infer m ::: b


mul : TermI
mul = Mu "times" (Lam "m" (Lam "n" (Case (Var "m") Zero "m" (Infer $ (plus :! Nat ~> Nat ~> Nat) `App` Infer (Var "n") `App` (Infer $ Var "times" `App` Infer (Var "m") `App` Infer (Var "n"))))))


DecEq LambdaType where
  decEq (x ~> y) (z ~> w) with (decEq x z)
    decEq (x ~> y) (z ~> w) | (No contra) = No (\ Refl => contra Refl)
    decEq (x ~> y) (z ~> w) | (Yes prf) with (decEq y w)
      decEq (z ~> w) (z ~> w) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (z ~> y) (z ~> w) | (Yes Refl) | (No contra) = No (\ Refl => contra Refl)
  decEq (x ~> y) Nat = No (\ x => case x of {})
  decEq (x ~> y) (z * w) = No (\ x => case x of {})
  decEq Nat (x ~> y) = No (\ x => case x of {})
  decEq Nat Nat = Yes Refl
  decEq Nat (x * y) = No (\ x => case x of {})
  decEq (x * y) (z ~> w) = No (\ x => case x of {})
  decEq (x * y) Nat = No (\ x => case x of {})
  decEq (x * y) (z * w) with (decEq x z)
    decEq (x * y) (z * w) | (No contra) = No (\ Refl => contra Refl)
    decEq (x * y) (z * w) | (Yes prf) with (decEq y w)
      decEq (x * y) (z * w) | (Yes prf) | (No contra) = No (\ Refl => contra Refl)
      decEq (z * w) (z * w) | (Yes Refl) | (Yes Refl) = Yes Refl

domEq : a ~> b = a' ~> b' -> a = a'
domEq Refl = Refl

rngEq : a ~> b = a' ~> b' -> b = b'
rngEq Refl = Refl

nNeqArr : Not (Nat = a ~> b)
nNeqArr Refl impossible

nNeqPair : Not (Nat = a * b)
nNeqPair Refl impossible

pairNeqArr : Not (x * z = a ~> b)
pairNeqArr Refl impossible

uniqHas : ctx `Has` (x, a) -> ctx `Has` (x, b) -> a = b
uniqHas Z Z = Refl
uniqHas Z (S f y) = absurd (f Refl)
uniqHas (S f y) Z = absurd (f Refl)
uniqHas (S f y) (S g z) = uniqHas y z

uniqHas' : Extensionality -> (y,z : ctx `Has` (x, a)) -> y = z
uniqHas' _   Z Z = Refl
uniqHas' _   Z (S f y) = absurd (f Refl)
uniqHas' _   (S f x) Z = absurd (f Refl)
uniqHas' ext (S f x) (S g y) =
  rewrite uniqHas' ext x y in
    rewrite the (f = g) (ext (\ xEqy => absurd (f xEqy))) in Refl

uniqSyn : ctx |- m ::: a -> ctx |- m ::: b -> a = b
uniqSyn (JudgeVar x) (JudgeVar y) = rewrite uniqHas x y in Refl
uniqSyn (JudgeApp x z) (JudgeApp y w) = rngEq (uniqSyn x y)
uniqSyn (JudgePair x z) (JudgePair y w) = rewrite uniqSyn x y in rewrite uniqSyn z w in Refl
uniqSyn (JudgeAssert x) (JudgeAssert y) = Refl

uniqInh : {auto ext : Extensionality} -> (z, w : ctx |= (m ::: a)) -> z = w
uniqSyn' : {auto ext : Extensionality} -> (x,y : ctx |- m ::: a) -> x = y
uniqSyn'' : {auto ext : Extensionality} -> (x : ctx |- m ::: a) -> (y : ctx |- m ::: b) -> x ~=~ y

uniqInh (JudgeLam x) (JudgeLam y) = rewrite uniqInh x y in Refl
uniqInh JudgeZero JudgeZero = Refl
uniqInh (JudgeSuc x) (JudgeSuc y) = rewrite uniqInh x y in Refl
uniqInh (JudgeMu  x) (JudgeMu  y) = rewrite uniqInh x y in Refl
uniqInh (JudgeProj1 x) (JudgeProj1 y) with (uniqSyn'' x y)
  uniqInh (JudgeProj1 x) (JudgeProj1 x) | Refl = Refl
uniqInh (JudgeProj2 x) (JudgeProj2 y) with (uniqSyn'' x y)
  uniqInh (JudgeProj2 x) (JudgeProj2 x) | Refl = Refl
uniqInh (JudgeCaseP x y) (JudgeCaseP z w) with (uniqSyn'' x z)
  uniqInh (JudgeCaseP x y) (JudgeCaseP x w) | Refl = rewrite uniqInh y w in Refl
uniqInh (JudgeCase x y z) (JudgeCase w v s) with (uniqSyn'' x w)
  uniqInh (JudgeCase x y z) (JudgeCase x v s) | Refl = rewrite uniqInh y v in rewrite uniqInh z s in Refl
uniqInh (JudgeInfer x Refl) (JudgeInfer y Refl) = rewrite uniqSyn' x y in Refl

uniqSyn' (JudgeVar x) (JudgeVar y) = rewrite uniqHas' ext x y in Refl
uniqSyn' (JudgeApp x z) (JudgeApp y w) with (uniqSyn'' x y)
  uniqSyn' (JudgeApp x z) (JudgeApp x w) | Refl with (uniqInh z w)
    uniqSyn' (JudgeApp x w) (JudgeApp x w) | Refl | Refl = Refl
uniqSyn' (JudgePair x z) (JudgePair y w) with (uniqSyn' x y)
  uniqSyn' (JudgePair x z) (JudgePair x w) | Refl with (uniqSyn' z w)
    uniqSyn' (JudgePair x w) (JudgePair x w) | Refl | Refl = Refl
uniqSyn' (JudgeAssert x) (JudgeAssert y) = rewrite uniqInh x y in Refl

uniqSyn'' {a} {b} x y with (uniqSyn x y)
  uniqSyn'' {a} {b = a} x y | Refl = uniqSyn' x y

extHas : Not (x = y)
      -> Not (a : LambdaType ** ctx `Has` (x,a))
      -> Not (a : LambdaType ** ctx :: (y,b) `Has` (x, a))
extHas f g (MkDPair b Z) = f Refl
extHas f g (MkDPair fst (S f1 z)) = g (MkDPair fst z)

lookup : (ctx : Inference.Context) -> (x : Id) -> Dec (a : _ ** ctx `Has` (x,a))
lookup Empty _ = No (\ x => case snd x of {})
lookup (y :: (z, w)) x with (decEq z x)
  lookup (y :: (z, w)) z | (Yes Refl) = Yes (MkDPair w Z)
  lookup (y :: (z, w)) x | (No contra) with (lookup y x)
    lookup (y :: (z, w)) x | (No contra) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (S (\ x => contra (sym x)) snd))
    lookup (y :: (z, w)) x | (No contra) | (No f) = No (\ (MkDPair fst snd) => case snd of
      Z => contra Refl
      (S g v) => f (MkDPair fst v)
      )

notArg : ctx |- l ::: a ~> b -> Not (ctx |= m ::: a) -> Not (b' : _ ** ctx |- l `App` m ::: b')
notArg x f (MkDPair fst (JudgeApp y z)) = f (rewrite domEq (uniqSyn x y) in z)

notSwitch : ctx |- m ::: a -> Not (a = b) -> Not (ctx |= (Infer m) ::: b)
notSwitch x f (JudgeInfer y prf) = f (rewrite uniqSyn x y in prf)

synthesize : (ctx : Inference.Context) -> (m : TermS) -> Dec (a : _ ** ctx |- m ::: a)
inherit : (ctx : Inference.Context) -> (m : TermI) -> (a : LambdaType) -> Dec (ctx |= m ::: a)

synthesize ctx (Var x) with (lookup ctx x)
  synthesize ctx (Var x) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (JudgeVar snd))
  synthesize ctx (Var x) | (No contra) = No (\ (MkDPair fst (JudgeVar y)) => contra (MkDPair fst y))
synthesize ctx (x `App` y) with (synthesize ctx x)
  synthesize ctx (x `App` y) | (No contra) = No (\ (MkDPair z (JudgeApp w v)) => contra (MkDPair _ w))
  synthesize ctx (x `App` y) | (Yes (MkDPair Nat snd)) = No (\ (MkDPair _ (JudgeApp l _)) => nNeqArr (uniqSyn snd l))
  synthesize ctx (x `App` y) | (Yes (MkDPair (z * w) snd)) = No (\ (MkDPair _ (JudgeApp l _)) => pairNeqArr (uniqSyn snd l))
  synthesize ctx (x `App` y) | (Yes (MkDPair (z ~> w) snd)) with (inherit ctx y z)
    synthesize ctx (x `App` y) | (Yes (MkDPair (z ~> w) snd)) | (Yes prf) = Yes (MkDPair w (JudgeApp snd prf))
    synthesize ctx (x `App` y) | (Yes (MkDPair (z ~> w) snd)) | (No contra) = No (notArg snd contra)
synthesize ctx (Pair x y) with (synthesize ctx x)
  synthesize ctx (Pair x y) | (No contra) = No (\ (MkDPair (a * b) (JudgePair z w)) => contra (MkDPair a z))
  synthesize ctx (Pair x y) | (Yes prf) with (synthesize ctx y)
    synthesize ctx (Pair x y) | (Yes prf) | (No contra) = No (\ (MkDPair (a * b) (JudgePair z w)) => contra (MkDPair b w))
    synthesize ctx (Pair x y) | (Yes (MkDPair fst snd)) | (Yes (MkDPair z w)) = Yes (MkDPair (fst * z) (JudgePair snd w))
synthesize ctx (x :! y) with (inherit ctx x y)
  synthesize ctx (x :! y) | (Yes prf) = Yes (MkDPair y (JudgeAssert prf))
  synthesize ctx (x :! y) | (No contra) = No (\ (MkDPair y (JudgeAssert z)) => contra z)

inherit ctx (Lam x y) (z ~> w) with (inherit (ctx :: (x,z)) y w)
  inherit ctx (Lam x y) (z ~> w) | (Yes prf) = Yes (JudgeLam prf)
  inherit ctx (Lam x y) (z ~> w) | (No contra) = No (\ (JudgeLam prf) => contra prf)
inherit ctx Zero Nat = Yes JudgeZero
inherit ctx (Suc x) Nat with (inherit ctx x Nat)
  inherit ctx (Suc x) Nat | (Yes prf) = Yes (JudgeSuc prf)
  inherit ctx (Suc x) Nat | (No contra) = No (\ (JudgeSuc prf) => contra prf)
inherit ctx (Case x y z w) a with (synthesize ctx x)
  inherit ctx (Case x y z w) a | (No contra) = No (\ (JudgeCase x' y' w') => contra (MkDPair Nat x'))
  inherit ctx (Case x y z w) a | (Yes (MkDPair (v ~> s) snd)) = No (\ (JudgeCase x' y' w') => nNeqArr (uniqSyn x' snd))
  inherit ctx (Case x y z w) a | (Yes (MkDPair (v * s) snd)) = No (\ (JudgeCase x' y' w') => nNeqPair (uniqSyn x' snd))
  inherit ctx (Case x y z w) a | (Yes (MkDPair Nat snd)) with (inherit ctx y a)
    inherit ctx (Case x y z w) a | (Yes (MkDPair Nat snd)) | (No contra) = No (\ (JudgeCase x' y' w') => contra y')
    inherit ctx (Case x y z w) a | (Yes (MkDPair Nat snd)) | (Yes prf) with (inherit (ctx :: (z, Nat)) w a)
      inherit ctx (Case x y z w) a | (Yes (MkDPair Nat snd)) | (Yes prf) | (No contra) = No (\ (JudgeCase x' y' w') => contra w')
      inherit ctx (Case x y z w) a | (Yes (MkDPair Nat snd)) | (Yes prf) | (Yes v) = Yes (JudgeCase snd prf v)
inherit ctx (Mu x y) a with (inherit (ctx :: (x, a)) y a)
  inherit ctx (Mu x y) a | (No contra) = No (\ (JudgeMu x) => contra x)
  inherit ctx (Mu x y) a | (Yes prf) = Yes (JudgeMu prf)
inherit ctx (Proj1 x) a with (synthesize ctx x)
  inherit ctx (Proj1 x) a | (Yes (MkDPair (y ~> z) snd)) = No (\ (JudgeProj1 x') => pairNeqArr (uniqSyn x' snd))
  inherit ctx (Proj1 x) a | (Yes (MkDPair Nat snd)) = No (\ (JudgeProj1 x') => nNeqPair (uniqSyn snd x'))
  inherit ctx (Proj1 x) a | (Yes (MkDPair (y * z) snd)) with (decEq y a)
    inherit ctx (Proj1 x) y | (Yes (MkDPair (y * z) snd)) | (Yes Refl) = Yes (JudgeProj1 snd)
    inherit ctx (Proj1 x) a | (Yes (MkDPair (y * z) snd)) | (No contra) = No (\ (JudgeProj1 x') => case (uniqSyn x' snd) of { Refl => contra Refl })
  inherit ctx (Proj1 x) a | (No contra) = No (\ (JudgeProj1 x') => contra (MkDPair _ x'))
inherit ctx (Proj2 x) a with (synthesize ctx x)
  inherit ctx (Proj2 x) a | (Yes (MkDPair (y ~> z) snd)) = No (\ (JudgeProj2 x') => pairNeqArr (uniqSyn x' snd))
  inherit ctx (Proj2 x) a | (Yes (MkDPair Nat snd)) = No (\ (JudgeProj2 x') => nNeqPair (uniqSyn snd x'))
  inherit ctx (Proj2 x) a | (Yes (MkDPair (y * z) snd)) with (decEq z a)
    inherit ctx (Proj2 x) z | (Yes (MkDPair (y * z) snd)) | (Yes Refl) = Yes (JudgeProj2 snd)
    inherit ctx (Proj2 x) a | (Yes (MkDPair (y * z) snd)) | (No contra) = No (\ (JudgeProj2 x') => case (uniqSyn x' snd) of { Refl => contra Refl })
  inherit ctx (Proj2 x) a | (No contra) = No (\ (JudgeProj2 x') => contra (MkDPair _ x'))
inherit ctx (CaseP x y z w) a with (synthesize ctx x)
  inherit ctx (CaseP x y z w) a | (No contra) = No (\ (JudgeCaseP x' w') => contra (MkDPair _ x'))
  inherit ctx (CaseP x y z w) a | (Yes (MkDPair (v ~> s) snd)) = No (\ (JudgeCaseP x' w') => pairNeqArr (uniqSyn x' snd))
  inherit ctx (CaseP x y z w) a | (Yes (MkDPair Nat snd)) = No (\ (JudgeCaseP x' w') => nNeqPair (uniqSyn snd x'))
  inherit ctx (CaseP x y z w) a | (Yes (MkDPair (v * s) snd)) with (inherit (ctx :: (y,v) :: (z,s)) w a)
    inherit ctx (CaseP x y z w) a | (Yes (MkDPair (v * s) snd)) | (Yes prf) = Yes (JudgeCaseP snd prf)
    inherit ctx (CaseP x y z w) a | (Yes (MkDPair (v * s) snd)) | (No contra) = No (\ (JudgeCaseP x' w') => case (uniqSyn x' snd) of { Refl => contra w' })
inherit ctx (Infer x) a with (synthesize ctx x)
  inherit ctx (Infer x) a | (No contra) = No (\ (JudgeInfer x Refl) => contra $ MkDPair a x)
  inherit ctx (Infer x) a | (Yes (MkDPair fst snd)) with (decEq fst a)
    inherit ctx (Infer x) a | (Yes (MkDPair fst snd)) | (Yes prf) = Yes (JudgeInfer snd prf)
    inherit ctx (Infer x) a | (Yes (MkDPair fst snd)) | (No contra) = No (\ (JudgeInfer x' prf) => case (uniqSyn x' snd) of {Refl => contra prf})
inherit ctx (Lam x y) Nat      = No (\ x => case x of {})
inherit ctx (Lam x y) (z * w)  = No (\ x => case x of {})
inherit ctx Zero      (x ~> y) = No (\ x => case x of {})
inherit ctx Zero      (x * y)  = No (\ x => case x of {})
inherit ctx (Suc x)   (y ~> z) = No (\ x => case x of {})
inherit ctx (Suc x)   (y * z)  = No (\ x => case x of {})

judgeTwoPlusTwo : Empty |- Inference.twoPlusTwo ::: Nat
judgeTwoPlusTwo =
  JudgeApp
    (JudgeApp
      (JudgeAssert
        (JudgeMu
          (JudgeLam (JudgeLam (JudgeCase (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeVar Z) Refl) (JudgeSuc (JudgeInfer (JudgeApp (JudgeApp (JudgeVar (S (\x => case x of {}) (S (\x => case x of {}) (S (\x => case x of {}) Z)))) (JudgeInfer (JudgeVar Z) Refl)) (JudgeInfer (JudgeVar (S (\x => case x of {}) Z)) Refl)) Refl))))))) (JudgeSuc (JudgeSuc JudgeZero))) (JudgeSuc (JudgeSuc JudgeZero))


judgeTwoPlusTwoCh : {a : LambdaType} -> Empty |- Inference.twoPlusTwoCh' {a} ::: Ch a
judgeTwoPlusTwoCh = JudgeApp (JudgeApp (JudgeAssert (JudgeLam (JudgeLam (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeApp (JudgeVar (S (\x => case x of {}) (S (\x => case x of {}) (S (\x => case x of {}) Z)))) (JudgeInfer (JudgeVar (S (\x => case x of {}) Z)) Refl)) (JudgeInfer (JudgeApp (JudgeApp (JudgeVar (S (\x => case x of {}) (S (\x => case x of {}) Z))) (JudgeInfer (JudgeVar (S (\x => case x of {}) Z)) Refl)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))))) (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))) (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))

judgeTwoPlusTwoCh' : Empty |- (Inference.twoPlusTwoCh `App` Inference.suc `App` Zero) ::: Nat
judgeTwoPlusTwoCh' = JudgeApp (JudgeApp (JudgeApp (JudgeApp (JudgeAssert (JudgeLam (JudgeLam (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeApp (JudgeVar (S (\x => case x of {}) (S (\x => case x of {}) (S (\x => case x of {}) Z)))) (JudgeInfer (JudgeVar (S (\x => case x of {}) Z)) Refl)) (JudgeInfer (JudgeApp (JudgeApp (JudgeVar (S (\x => case x of {}) (S (\x => case x of {}) Z))) (JudgeInfer (JudgeVar (S (\x => case x of {}) Z)) Refl)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))))) (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))) (JudgeLam (JudgeLam (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeApp (JudgeVar (S (\x => case x of {}) Z)) (JudgeInfer (JudgeVar Z) Refl)) Refl)) Refl)))) (JudgeLam (JudgeSuc (JudgeInfer (JudgeVar Z) Refl)))) JudgeZero

synthTwoPlusTwoCh : {auto ext : Extensionality} -> synthesize Empty (Inference.twoPlusTwoCh `App` Inference.suc `App` Zero) = Yes (MkDPair MoreMul.Nat Inference.judgeTwoPlusTwoCh')
synthTwoPlusTwoCh with (synthesize Empty (Inference.twoPlusTwoCh `App` Inference.suc `App` Zero))
  synthTwoPlusTwoCh | (Yes (MkDPair fst snd)) with (uniqSyn snd judgeTwoPlusTwoCh')
    synthTwoPlusTwoCh | (Yes (MkDPair Nat snd)) | Refl = rewrite uniqSyn' snd judgeTwoPlusTwoCh' in Refl
  synthTwoPlusTwoCh | (No contra) = case contra (MkDPair MoreMul.Nat Inference.judgeTwoPlusTwoCh') of {}

data IsNo : Dec a -> Type where
  MkIsNo : IsNo (No whyNot)

plusS : TermS
plusS = plus :! Nat ~> Nat ~> Nat

test1 : IsNo (synthesize Empty (Lam "x" (Infer (Var "y")) :! Nat ~> Nat))
test1 = MkIsNo

test2 : IsNo (synthesize Empty ((Inference.plus :! (Nat ~> Nat ~> Nat)) `App` Inference.suc))
test2 = MkIsNo

test3 : IsNo (synthesize Empty (Inference.plusS `App` Inference.suc `App` Inference.two))
test3 = MkIsNo

test4 : IsNo (synthesize Empty ((Inference.two :! Nat) `App` Inference.two))
test4 = MkIsNo

test5 : IsNo (synthesize Empty (Inference.chTwo :! Nat))
test5 = MkIsNo

test6 : IsNo (synthesize Empty (Zero :! Nat ~> Nat))
test6 = MkIsNo

test7 : IsNo (synthesize Empty (Inference.two :! Nat ~> Nat))
test7 = MkIsNo

test8 : IsNo (synthesize Empty (Suc (Inference.chTwo) :! Nat) )
test8 = MkIsNo

test9 : IsNo (synthesize Empty (Case (Inference.chTwo :! Ch Nat) Zero "x" (Infer (Var "x")) :! Nat))
test9 = MkIsNo

test10 : IsNo (synthesize Empty (Case (Inference.chTwo :! Nat) Zero "x" (Infer (Var "x")) :! Nat))
test10 = MkIsNo

test11 : IsNo (synthesize Empty (Lam "x" (Infer (Var "x")) :! Nat ~> (Nat ~> Nat)))
test11 = MkIsNo

eraseCtx : Inference.Context -> MoreMul.Context
eraseCtx Empty = Empty
eraseCtx (x :: (_, z)) = eraseCtx x :: z

eraseLookup : ctx `Inference.Has` (x,a) -> eraseCtx ctx `Has` a
eraseLookup Z = Z
eraseLookup (S f y) = S (eraseLookup y)

eraseTypeS : ctx |- m ::: a -> eraseCtx ctx |- a
eraseTypeI : ctx |= m ::: a -> eraseCtx ctx |- a

eraseTypeS (JudgeVar x) = Var (eraseLookup x)
eraseTypeS (JudgeApp x y) = App (eraseTypeS x) (eraseTypeI y)
eraseTypeS (JudgePair x y) = Pair (eraseTypeS x) (eraseTypeS y)
eraseTypeS (JudgeAssert x) = eraseTypeI x

eraseTypeI (JudgeLam x) = Lam (eraseTypeI x)
eraseTypeI JudgeZero = Zero
eraseTypeI (JudgeSuc x) = Suc (eraseTypeI x)
eraseTypeI (JudgeCase x y z) = Case (eraseTypeS x) (eraseTypeI y) (eraseTypeI z)
eraseTypeI (JudgeMu x) = Mu (eraseTypeI x)
eraseTypeI (JudgeProj1 x) = Proj1 (eraseTypeS x)
eraseTypeI (JudgeProj2 x) = Proj2 (eraseTypeS x)
eraseTypeI (JudgeCaseP x y) = CaseP (eraseTypeS x) (eraseTypeI y)
eraseTypeI (JudgeInfer x Refl) = eraseTypeS x

test12 : eraseTypeS Inference.judgeTwoPlusTwo = MoreMul.twoPlusTwo
test12 = Refl

test13 : eraseTypeS Inference.judgeTwoPlusTwoCh = MoreMul.twoPlusTwoCh
test13 = Refl

