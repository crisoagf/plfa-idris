module MoreSum
import Data.Nat
import Data.Nat.Order
import Decidable.Decidable

infix 4 |-
infixl 5 ::

infixr 7 ~>
infixl 7 `App`

prefix 0 #

data LambdaType : Type where
  (~>) : LambdaType -> LambdaType -> LambdaType
  Nat : LambdaType
  (+) : LambdaType -> LambdaType -> LambdaType

data Context : Type where
  Empty : Context
  (::) : Context -> LambdaType -> Context

test : Context
test = Empty :: Nat ~> Nat :: Nat

data Has : Context -> LambdaType -> Type where
  Z : Has (ctx :: a) a
  S : Has ctx a -> Has (ctx :: b) a

test1 : MoreSum.test `Has` Nat
test1 = Z

test2 : MoreSum.test `Has` Nat ~> Nat
test2 = S Z

data (|-) : Context -> LambdaType -> Type where
  Var : ctx `Has` a -> ctx |- a
  Lam : ctx :: a |- b -> ctx |- a ~> b
  App : ctx |- a ~> b -> ctx |- a -> ctx |- b
  Zero : ctx |- Nat
  Suc : ctx |- Nat -> ctx |- Nat
  Case : ctx |- Nat -> ctx |- a -> ctx :: Nat |- a -> ctx |- a
  Mu : ctx :: a |- a -> ctx |- a
  Inj1 : ctx |- a -> ctx |- a + b
  Inj2 : ctx |- b -> ctx |- a + b
  Either : ctx |- a + b -> ctx :: a |- c -> ctx :: b |- c -> ctx |- c

test3 : MoreSum.test |- Nat
test3 = Zero

test4 : MoreSum.test |- Nat ~> Nat
test4 = Var (S Z)

test5 : MoreSum.test |- Nat
test5 = Var (S Z) `App` Var Z

test6 : MoreSum.test |- Nat
test6 = Var (S Z) `App` (Var (S Z) `App` Var Z)

test7 : Empty :: Nat ~> Nat |- Nat ~> Nat
test7 = Lam (Var (S Z) `App` (Var (S Z) `App` Var Z))

test8 : Empty |- (Nat ~> Nat) ~> Nat ~> Nat
test8 = Lam (Lam (Var (S Z) `App` (Var (S Z) `App` Var Z)))

test9' : Empty |- ((Nat ~> Nat) ~> Nat ~> Nat) + Nat
test9' = Inj1 test8

test10' : Empty :: Nat + b |- Nat
test10' = Either (Var Z) (Var Z) Zero

length : Context -> Prelude.Nat
length Empty = Z
length (ctx :: _) = S (length ctx)

lookup : {ctx : Context} -> {n : Nat} -> (p : n `LT` length ctx) -> LambdaType
lookup {ctx = _::a} {n = 0} (LTESucc LTEZero) = a
lookup {ctx = ctx::_} {n = S k} (LTESucc x) = lookup x

count : {ctx : Context} -> {n : Nat} -> (p : n `LT` length ctx) -> ctx `Has` lookup {ctx} p
count {ctx = _::_} {n = 0} (LTESucc LTEZero) = Z
count {ctx = ctx::_} {n = (S k)} (LTESucc p) = S (count p)

(#) : {ctx  : Context} -> (n : Nat) -> {auto nIndex : n `LT` length ctx} -> ctx |- lookup {ctx} nIndex
(#) n {nIndex} = Var (count nIndex)

two : ctx |- Nat
two = Suc (Suc Zero)

plus : {ctx : Context} -> ctx |- Nat ~> Nat ~> Nat
plus = Mu $ Lam $ Lam $ Case (# 1) (# 0) (Suc ((# 3) `App` (# 0) `App` (# 1)))

twoPlusTwo : {ctx : Context} -> ctx |- Nat
twoPlusTwo = plus `App` two `App` two

Ch : LambdaType -> LambdaType
Ch a = (a ~> a) ~> a ~> a

twoCh : {ctx : Context} -> {a : LambdaType} -> ctx |- Ch a
twoCh = Lam (Lam ((# 1) `App` ((# 1) `App` (# 0))))

plusCh : {ctx : Context} -> {a : LambdaType} -> ctx |- Ch a ~> Ch a ~> Ch a
plusCh = Lam (Lam (Lam (Lam ((# 3) `App` (# 1) `App` ((# 2) `App` (# 1) `App` (# 0))))))

suc : {ctx : Context} -> ctx |- Nat ~> Nat
suc = Lam (Suc (# 0))

twoPlusTwoCh : {ctx : Context} -> {a : LambdaType} -> ctx |- Ch a
twoPlusTwoCh = plusCh `App` twoCh `App` twoCh

churchToNative : {ctx : Context} -> ctx |- Ch Nat ~> Nat
churchToNative = Lam ((# 0) `App` suc `App` Zero)

multCh : {ctx : Context} -> {a : LambdaType} -> ctx |- Ch a ~> Ch a ~> Ch a
multCh = Lam (Lam (Lam (Lam ((# 3) `App` ((# 2) `App` (# 1)) `App` (# 0)))))

ext : ({0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a) -> ctx :: b `Has` a -> ctx' :: b `Has` a
ext _ Z = Z
ext f (S x) = S (f x)

rename : ({0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a) -> ctx |- a -> ctx' |- a
rename f (Var x) = Var (f x)
rename f (Lam x) = Lam (rename (ext f) x)
rename f (x `App` y) = rename f x `App` rename f y
rename f Zero = Zero
rename f (Suc x) = Suc (rename f x)
rename f (Case x y z) = Case (rename f x) (rename f y) (rename (ext f) z)
rename f (Mu x) = Mu (rename (ext f) x)
rename f (Inj1 x) = Inj1 (rename f x)
rename f (Inj2 x) = Inj2 (rename f x)
rename f (Either x y z) = Either (rename f x) (rename (ext f) y) (rename (ext f) z)

exts : ({0 a : LambdaType} -> ctx `Has` a -> ctx' |- a) -> ctx :: b `Has` a -> ctx' :: b |- a
exts f Z = Var Z
exts f (S x) = rename S (f x)

subst : ({0 a : LambdaType} -> ctx `Has` a -> ctx' |- a) -> ctx |- a -> ctx' |- a
subst f (Var x) = f x
subst f (Lam x) = Lam (subst (exts f) x)
subst f (x `App` y) = subst f x `App` subst f y
subst f Zero = Zero
subst f (Suc x) = Suc (subst f x)
subst f (Case x y z) = Case (subst f x) (subst f y) (subst (exts f) z)
subst f (Mu x) = Mu (subst (exts f) x)
subst f (Inj1 x) = Inj1 (subst f x)
subst f (Inj2 x) = Inj2 (subst f x)
subst f (Either x y z) = Either (subst f x) (subst (exts f) y) (subst (exts f) z)

replace : ctx :: b |- a -> ctx |- b -> ctx |- a
replace x y = subst f x
  where
   f : ctx :: b `Has` k -> ctx |- k
   f Z = y
   f (S z) = Var z

m2 : Empty :: Nat ~> Nat |- Nat ~> Nat
m2 = Lam ((# 1) `App` ((# 1) `App` (# 0)))

m3 : Empty |- Nat ~> Nat
m3 = Lam (Suc (# 0))

m4 : Empty |- Nat ~> Nat
m4 = Lam (Lam (Suc (# 0)) `App` (Lam (Suc (# 0)) `App` (# 0)))

test9 : replace MoreSum.m2 MoreSum.m3 = MoreSum.m4
test9 = Refl

m5 : Empty :: Nat ~> Nat :: Nat |- (Nat ~> Nat) ~> Nat
m5 = Lam ((# 0) `App` (# 1))

m6 : Empty :: Nat ~> Nat |- Nat
m6 = (# 0) `App` Zero

m7 : Empty :: Nat ~> Nat |- (Nat ~> Nat) ~> Nat
m7 = Lam ((# 0) `App` ((# 1) `App` Zero))

test10 : replace MoreSum.m5 MoreSum.m6 = MoreSum.m7
test10 = Refl

data Value : ctx |- a -> Type where
  VLam : {n : ctx :: a |- b} -> Value (Lam n)
  VZero : Value Zero
  VSuc : {n : ctx |- Nat} -> Value n -> Value (Suc n)
  VInj1 : Value v -> Value (Inj1 v)
  VInj2 : Value v -> Value (Inj2 v)

infix 2 -=>
infix 2 -=>>

data (-=>) : ctx |- a -> ctx |- a -> Type where
  IntroAppLeft : left -=> left' -> left `App` middle -=> left' `App` middle
  IntroAppRight : Value left -> middle -=> middle' -> left `App` middle -=> left `App` middle'
  BetaLam : Value w -> Lam n `App` w -=> replace n w
  IntroSuc : m -=> m' -> Suc m -=> Suc m'
  IntroCase : l -=> l' -> Case l m n -=> Case l' m n
  BetaZero : Case Zero m n -=> m
  BetaSuc : Value v -> Case (Suc v) m n -=> replace n v
  BetaMu : Mu n -=> replace n (Mu n)
  IntroInj1 : left -=> left' -> Inj1 left -=> Inj1 left'
  IntroInj2 : left -=> left' -> Inj2 left -=> Inj2 left'
  IntroEither : left -=> left' -> Either left middle right -=> Either left' middle right
  BetaLeft : Value v -> Either (Inj1 v) x y -=> replace x v
  BetaRight : Value v -> Either (Inj2 v) x y -=> replace y v

data (-=>>) : ctx |- a -> ctx |- a -> Type where
  Refl : m -=>> m
  Trans : (l : ctx |- a) -> l -=> m -> m -=>> n -> l -=>> n

test11 : MoreSum.twoCh `App` MoreSum.suc `App` Zero {ctx = Empty} -=>> MoreSum.two
test11 =
  Trans (twoCh `App` suc `App` Zero) (IntroAppLeft (BetaLam VLam))
  $ Trans (Lam (suc `App` (suc `App` (# 0))) `App` Zero) (BetaLam VZero)
  $ Trans (suc `App` (suc `App` Zero)) (IntroAppRight VLam (BetaLam VZero))
  $ Trans (suc `App` Suc Zero) (BetaLam (VSuc VZero))
  $ Refl

test12 : MoreSum.plus {ctx = Empty} `App` MoreSum.two `App` MoreSum.two -=>> Suc (Suc (Suc (Suc Zero)))
test12 =
  Trans (plus `App` two `App` two) (IntroAppLeft (IntroAppLeft BetaMu))
  $ Trans (Lam (Lam (Case (# 1) (# 0) (Suc (plus `App` (# 0) `App` (# 1))))) `App` two `App` two) (IntroAppLeft (BetaLam (VSuc (VSuc VZero))))
  $ Trans (Lam (Case two (# 0) (Suc (plus `App` (# 0) `App` (# 1)))) `App` two) (BetaLam (VSuc (VSuc VZero)))
  $ Trans (Case two two (Suc (plus `App` (# 0) `App` two))) (BetaSuc (VSuc VZero))
  $ Trans (Suc (plus `App` Suc Zero `App` two)) (IntroSuc (IntroAppLeft (IntroAppLeft BetaMu)))
  $ Trans (Suc (Lam (Lam (Case (# 1) (# 0) (Suc (plus `App` (# 0) `App` (# 1))))) `App` Suc Zero `App` two)) (IntroSuc (IntroAppLeft (BetaLam (VSuc VZero))))
  $ Trans (Suc (Lam (Case (Suc Zero) (# 0) (Suc (plus `App` (# 0) `App` (# 1)))) `App` two)) (IntroSuc (BetaLam (VSuc (VSuc VZero))))
  $ Trans (Suc (Case (Suc Zero) two (Suc (plus `App` (# 0) `App` two)))) (IntroSuc (BetaSuc VZero))
  $ Trans (Suc (Suc (plus `App` Zero `App` two))) (IntroSuc (IntroSuc (IntroAppLeft (IntroAppLeft BetaMu))))
  $ Trans (Suc (Suc (Lam (Lam (Case (# 1) (# 0) (Suc (plus `App` (# 0) `App` (# 1))))) `App` Zero `App` two))) (IntroSuc (IntroSuc (IntroAppLeft (BetaLam VZero))))
  $ Trans (Suc (Suc (Lam (Case Zero (# 0) (Suc (plus `App` (# 0) `App` (# 1)))) `App` two))) (IntroSuc (IntroSuc (BetaLam (VSuc (VSuc VZero)))))
  $ Trans (Suc (Suc (Case Zero two (Suc (plus `App` (# 0) `App` two))))) (IntroSuc (IntroSuc BetaZero))
  $ Refl

valuesDontReduce : Value m -> Not (m -=> n)
valuesDontReduce (VSuc x) (IntroSuc y) = valuesDontReduce x y
valuesDontReduce (VInj1 x) (IntroInj1 y) = valuesDontReduce x y
valuesDontReduce (VInj2 x) (IntroInj2 y) = valuesDontReduce x y

reduceNotValue : m -=> n -> Not (Value m)
reduceNotValue x y = valuesDontReduce y x

data Progress : Empty |- a -> Type where
  Step : {n : Empty |- a} -> m -=> n -> Progress m
  Done : Value m -> Progress m

progress : (m : Empty |- a) -> Progress m
progress (Var Z) impossible
progress (Var (S x)) impossible
progress (Lam x) = Done VLam
progress (x `App` y) with (progress x)
  progress (x `App` y) | (Step z) = Step (IntroAppLeft z)
  progress (x `App` y) | (Done z) with (progress y)
    progress (x `App` y) | (Done z) | (Step w) = Step (IntroAppRight z w)
    progress ((Lam n) `App` y) | (Done VLam) | (Done w) = Step (BetaLam w)
progress Zero = Done VZero
progress (Suc x) with (progress x)
  progress (Suc x) | (Step y) = Step (IntroSuc y)
  progress (Suc x) | (Done y) = Done (VSuc y)
progress (Case x y z) = assert_total $ case progress x of
                             (Step w) => Step (IntroCase w)
                             (Done VZero) => Step BetaZero
                             (Done (VSuc w)) => Step (BetaSuc w)
                             (Done VLam) impossible
progress (Mu x) = Step BetaMu
progress (Inj1 x) with (progress x)
  progress (Inj1 x) | (Step y) = Step (IntroInj1 y)
  progress (Inj1 x) | (Done y) = Done (VInj1 y)
progress (Inj2 x) with (progress x)
  progress (Inj2 x) | (Step y) = Step (IntroInj2 y)
  progress (Inj2 x) | (Done y) = Done (VInj2 y)
progress (Either x y z) with (progress x)
  progress (Either x y z) | (Step w) = Step (IntroEither w)
  progress (Either x y z) | (Done w) = assert_total $ case w of
                                       (VInj1 v) => Step (BetaLeft v)
                                       (VInj2 v) => Step (BetaRight v)

data ReducesIn : Nat -> (ctx |- a) -> (ctx |- a) -> Type where
  Finished : Value m -> ReducesIn (S k) m m
  OutOfGas : ReducesIn 0 m m
  ReduceStep : m -=> n -> ReducesIn k n o -> ReducesIn (S k) m o

eval : (n : Nat) -> (l : Empty |- a) -> (m : Empty |- a ** ReducesIn n l m)
eval 0 l = MkDPair l OutOfGas
eval (S k) l with (progress l)
  eval (S k) l | (Done x) = MkDPair l (Finished x)
  eval (S k) l | (Step {n} x) with (eval k n)
    eval (S k) l | (Step {n = n} x) | (MkDPair fst snd) = MkDPair fst (ReduceStep x snd)

swapE : {a, b : LambdaType} -> Empty |- a + b ~> b + a
swapE = Lam (Either (# 0) (Inj2 (# 0)) (Inj1 (# 0)))

test13 : eval 3 (Mu (Suc (# 0))) = MkDPair (Suc (Suc (Suc (Mu (Suc (Var Z))))))
  ( ReduceStep BetaMu
  $ ReduceStep (IntroSuc BetaMu)
  $ ReduceStep (IntroSuc (IntroSuc BetaMu))
  OutOfGas )
test13 = Refl

test14 : eval 100 (MoreSum.twoCh `App` MoreSum.suc `App` Zero) = MkDPair (Suc (Suc Zero))
  ( ReduceStep (IntroAppLeft (BetaLam VLam))
  $ ReduceStep (BetaLam VZero)
  $ ReduceStep (IntroAppRight VLam (BetaLam VZero))
  $ ReduceStep (BetaLam (VSuc VZero))
  $ Finished (VSuc (VSuc VZero))
  )
test14 = Refl


test15 : eval 100 (MoreSum.plus `App` MoreSum.two `App` MoreSum.two) = MkDPair (Suc (Suc (Suc (Suc Zero))))
  ( ReduceStep (IntroAppLeft (IntroAppLeft BetaMu))
  $ ReduceStep (IntroAppLeft (BetaLam (VSuc (VSuc VZero))))
  $ ReduceStep (BetaLam (VSuc (VSuc VZero)))
  $ ReduceStep (BetaSuc (VSuc VZero))
  $ ReduceStep (IntroSuc (IntroAppLeft (IntroAppLeft BetaMu)))
  $ ReduceStep (IntroSuc (IntroAppLeft (BetaLam (VSuc VZero))))
  $ ReduceStep (IntroSuc (BetaLam (VSuc (VSuc VZero))))
  $ ReduceStep (IntroSuc (BetaSuc VZero))
  $ ReduceStep (IntroSuc (IntroSuc (IntroAppLeft (IntroAppLeft BetaMu))))
  $ ReduceStep (IntroSuc (IntroSuc (IntroAppLeft (BetaLam VZero))))
  $ ReduceStep (IntroSuc (IntroSuc (BetaLam (VSuc (VSuc VZero)))))
  $ ReduceStep (IntroSuc (IntroSuc BetaZero))
  $ Finished (VSuc (VSuc (VSuc (VSuc VZero))))
  )
test15 = Refl

