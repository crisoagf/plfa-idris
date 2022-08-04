module Untyped
import Isomorphism
import Data.Nat

%default total

infix 4 |-
infixl 5 ::
infixl 7 `App`
infixl 7 `AppN`
infixl 7 >>

public export
data LambdaType : Type where
  Star : LambdaType

typeIsoUnit : Iso LambdaType ()
typeIsoUnit = MkIso (\ Star => ()) (\ () => Star) (\ Star => Refl) (\ () => Refl)

public export
data Context : Type where
  Empty : Context
  (::) : Context -> LambdaType -> Context

fromCtx : Context -> Nat
fromCtx Empty = 0
fromCtx (x :: Star) = S (fromCtx x)

toCtx : Nat -> Context
toCtx 0 = Empty
toCtx (S k) = toCtx k :: Star

fromToCtx : (x : Context) -> toCtx (fromCtx x) = x
fromToCtx Empty = Refl
fromToCtx (x :: Star) = rewrite fromToCtx x in Refl

toFromCtx : (y : Nat) -> fromCtx (toCtx y) = y
toFromCtx 0 = Refl
toFromCtx (S k) = rewrite toFromCtx k in Refl

ctxIsoNat : Iso Context Nat
ctxIsoNat = MkIso fromCtx toCtx fromToCtx toFromCtx

public export
data Has : (0 _ : Context) -> (0 _ : LambdaType) -> Type where
  Z : ctx :: a `Has` a
  S : ctx `Has` a -> ctx :: b `Has` a

public export
data (|-) : (0 _ : Context) -> (0 _ : LambdaType) -> Type where
  Var : ctx `Has` a -> ctx |- a
  Lam : ctx :: Star |- Star -> ctx |- Star
  App : ctx |- Star -> ctx |- Star -> ctx |- Star

public export
length : Context -> Nat
length Empty = 0
length (x :: y) = S (length x)

public export
va : {ctx : Context} -> (n : Nat) -> {auto l : length ctx `GT` n} -> ctx `Has` Star
va {ctx = Empty} n {l = l} impossible
va {ctx = (x :: Star)} 0 {l = (LTESucc z)} = Z
va {ctx = (x :: Star)} (S k) {l = (LTESucc z)} = S (va k)

public export
var : {ctx : Context} -> (n : Nat) -> {auto l : length ctx `GT` n} -> ctx |- Star
var n = Var (va n)

public export
twoCh : {ctx : Context} -> ctx |- Star
twoCh = Lam (Lam (var 1 `App` (var 1 `App` var 0)))

fourCh : {ctx : Context} -> ctx |- Star
fourCh = Lam (Lam (var 1 `App` (var 1 `App` (var 1 `App` (var 1 `App` var 0)))))

public export
plusCh : {ctx : Context} -> ctx |- Star
plusCh = Lam (Lam (Lam (Lam (var 3 `App` var 1 `App` (var 2 `App` var 1 `App` var 0)))))

twoPlusTwoCh : {ctx : Context} -> ctx |- Star
twoPlusTwoCh = plusCh `App` twoCh `App` twoCh

public export
ext : ({0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a)
   -> {0 a, b : LambdaType} -> ctx :: b `Has` a -> ctx' :: b `Has` a
ext f Z = Z
ext f (S x) = S (f x)

public export
rename : ({0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a)
      -> {0 a : LambdaType} -> ctx |- a -> ctx' |- a
rename f (Var x) = Var (f x)
rename f (Lam x) = Lam (rename (ext f) x)
rename f (x `App` y) = rename f x `App` rename f y

public export
exts : ({0 a : LambdaType} -> ctx `Has` a -> ctx' |- a)
    -> {0 a, b : LambdaType} -> ctx :: b `Has` a -> ctx' :: b |- a
exts f Z = Var Z
exts f (S x) = rename S (f x)

public export
subst : ({0 a : LambdaType} -> ctx `Has` a -> ctx' |- a)
     -> {0 a : LambdaType} -> ctx |- a -> ctx' |- a
subst f (Var x) = f x
subst f (Lam x) = Lam (subst (exts f) x)
subst f (x `App` y) = subst f x `App` subst f y

public export
substZero : (m : ctx |- b) -> (ctx :: b `Has` a) -> ctx |- a
substZero x Z = x
substZero x (S y) = Var y

public export
replace : ctx :: b |- a -> ctx |- b -> ctx |- a
replace x y = subst (substZero y) x

mutual
  public export
  data Neutral : ctx |- a -> Type where
    VarN : (x : ctx `Has` a) -> Neutral (Var x)
    AppN : Neutral l -> Normal m -> Neutral (App l m)
  
  public export
  data Normal : ctx |- a -> Type where
    NeutralN : Neutral m -> Normal m
    LamN : Normal m -> Normal (Lam m)

public export
varN : {ctx : Context} -> (n : Nat) -> {auto l : length ctx `GT` n} -> Neutral (var {ctx} n)
varN n = VarN (va n)

varN' : {ctx : Context} -> (n : Nat) -> {auto l : length ctx `GT` n} -> Normal (var {ctx} n)
varN' n = NeutralN $ VarN (va n)

twoNormal : Normal Untyped.twoCh
twoNormal = LamN $ LamN $ NeutralN $ VarN (S Z) `AppN` NeutralN (VarN (S Z) `AppN` NeutralN (VarN Z))

plusNormal : Normal Untyped.plusCh
plusNormal = LamN $ LamN $ LamN $ LamN $ NeutralN $
  VarN (S (S (S Z)))
  `AppN` NeutralN (VarN (S Z))
  `AppN` NeutralN ((VarN (S (S Z)) `AppN` NeutralN (VarN (S Z))) `AppN` NeutralN (VarN Z))


infix 2 -=>
infix 2 -=!>
infix 2 -=!!>
infix 2 -=>>

public export
data (-=>) : ctx |- a -> ctx |- a -> Type where
  IntroAppLeft  : {l,l' : _} -> l -=> l' -> l `App` m -=> l' `App` m
  IntroAppRight : {m, m' : _} -> m -=> m' -> l `App` m -=> l `App` m'
  BetaLam : Lam n `App` m -=> replace n m
  IntroLam : n -=> n' -> Lam n -=> Lam n'

data (-=!>) : ctx |- a -> ctx |- a -> Type where
  IntroAppLeft1  : l -=!> l' -> l `App` m -=!> l' `App` m
  IntroAppRight1 : m -=!> m' -> l `App` m -=!> l `App` m'
  BetaLam1 : Normal n -> Normal m -> Lam n `App` m -=!> replace n m
  IntroLam1 : n -=!> n' -> Lam n -=!> Lam n'

data (-=!!>) : ctx |- a -> ctx |- a -> Type where
  IntroAppLeft2  : l -=!!> l' -> l `App` m -=!!> l' `App` m
  IntroAppRight2 : m -=!!> m' -> l `App` m -=!!> l `App` m'
  BetaLam2 : Normal n -> Normal m -> Lam n `App` m -=!!> replace n m

lemma : (m : ctx |- Star ** (Lam (Lam (Lam ((Lam (Lam (Var (S Z) `App` (Var (S Z) `App` Var Z))) `App` Var (S Z)) `App` ((Var (S (S Z)) `App` Var (S Z)) `App` Var Z)))) `App` Lam (Lam (Var (S Z) `App` (Var (S Z) `App` Var Z)))) -=!!> m) -> Void
lemma (MkDPair fst snd) = case snd of
  (IntroAppLeft2 x) impossible
  (IntroAppRight2 x) impossible
  (BetaLam2 x y) => case x of
    (LamN (LamN (NeutralN ((z `AppN` v) `AppN` w)))) impossible

twoPlusTwoChRed :
  ( Untyped.twoPlusTwoCh -=!!> Lam (Lam (Lam (Untyped.twoCh `App` Untyped.var 1 `App` (Untyped.var 2 `App` Untyped.var 1 `App` Untyped.var 0)))) `App` Untyped.twoCh
  , Not (m : ctx |- Star ** Lam (Lam (Lam (Untyped.twoCh `App` Untyped.var 1 `App` (Untyped.var 2 `App` Untyped.var 1 `App` Untyped.var 0)))) `App` Untyped.twoCh -=!!> m)
  )
twoPlusTwoChRed =
  ( IntroAppLeft2 (BetaLam2 (unLamN plusNormal) twoNormal)
  , lemma
  )
  where
    unLamN : Normal (Lam (Lam m)) -> Normal (Lam m)
    unLamN (LamN x) = x

infixr 2 `Trans`

public export
data (-=>>) : ctx |- a -> ctx |- a -> Type where
  Refl : m -=>> m
  Trans : {m : _} -> l -=> m -> m -=>> n -> l -=>> n

twoPlusTwoEqFour : {ctx : _} -> Untyped.twoPlusTwoCh {ctx} -=>> Untyped.fourCh
twoPlusTwoEqFour
  = IntroAppLeft BetaLam
  `Trans` BetaLam
  `Trans` IntroLam (IntroLam (IntroAppRight $ IntroAppLeft BetaLam))
  `Trans` IntroLam (IntroLam (IntroAppRight BetaLam))
  `Trans` IntroLam (IntroLam (IntroAppLeft BetaLam))
  `Trans` IntroLam (IntroLam BetaLam)
  `Trans` Refl


public export
data Progress : ctx |- a -> Type where
  Step : {n : ctx |- a} -> m -=> n -> Progress m
  Done : Normal m -> Progress m

export
progress : (m : ctx |- a) -> Progress m
progress (Var x) = Done (NeutralN (VarN x))
progress (Lam x) with (progress x)
  progress (Lam x) | (Step y) = Step (IntroLam y)
  progress (Lam x) | (Done y) = Done (LamN y)
progress ((Var x) `App` y) with (progress y)
  progress ((Var x) `App` y) | (Step z) = Step (IntroAppRight z)
  progress ((Var x) `App` y) | (Done z) = Done (NeutralN (VarN x `AppN` z))
progress ((Lam x) `App` y) = Step BetaLam
progress (l@(x `App` z) `App` y) with (progress l)
  progress (l@(x `App` z) `App` y) | (Step w) = Step (IntroAppLeft w)
  progress (l@(x `App` z) `App` y) | (Done w) with (progress y)
    progress (l@(x `App` z) `App` y) | (Done w) | (Step v) = Step (IntroAppRight v)
    progress (l@(x `App` z) `App` y) | (Done (NeutralN w)) | (Done v) = Done (NeutralN $ w `AppN` v)

data ReducesIn : Nat -> (ctx |- a) -> (ctx |- a) -> Type where
  Finished : Normal m -> ReducesIn (S k) m m
  OutOfGas : ReducesIn 0 m m
  ReduceStep : m -=> n -> ReducesIn k n o -> ReducesIn (S k) m o

export
eval : (n : Nat) -> (l : ctx |- a) -> (m : ctx |- a ** ReducesIn n l m)
eval 0 l = MkDPair l OutOfGas
eval (S k) l with (progress l)
  eval (S k) l | (Step {n} x) with (eval k n)
    eval (S k) l | (Step x) | (MkDPair fst snd) = MkDPair fst (ReduceStep x snd)
  eval (S k) l | (Done x) = MkDPair l (Finished x)

test : eval 100 Untyped.twoPlusTwoCh = MkDPair Untyped.fourCh
  (ReduceStep (IntroAppLeft BetaLam)
  (ReduceStep BetaLam
  (ReduceStep (IntroLam (IntroLam (IntroAppLeft BetaLam)))
  (ReduceStep (IntroLam (IntroLam BetaLam))
  (ReduceStep (IntroLam (IntroLam (IntroAppRight (IntroAppRight (IntroAppLeft BetaLam)))))
  (ReduceStep (IntroLam (IntroLam (IntroAppRight (IntroAppRight BetaLam))))
  (Finished (LamN (LamN (NeutralN (VarN (S Z) `AppN` NeutralN (VarN (S Z) `AppN` NeutralN (VarN (S Z) `AppN` NeutralN (VarN (S Z) `AppN` NeutralN (VarN Z)))))))))))))))
test = Refl

zeroSc : {ctx : Context} -> ctx |- Star
zeroSc = Lam . Lam $ var 0

sucSc : {ctx : Context} -> ctx |- Star -> ctx |- Star
sucSc m = (Lam . Lam . Lam $ var 1 `App` var 2) `App` m

caseSc : {ctx : Context} -> ctx |- Star -> ctx |- Star -> ctx :: Star |- Star -> ctx |- Star
caseSc x y z = x `App` Lam z `App` y

test1 : eval 100 (Untyped.sucSc Untyped.zeroSc) = MkDPair (Lam (Lam (Var (S Z) `App` Lam (Lam (Var Z))))) (ReduceStep BetaLam (Finished (LamN (LamN (NeutralN (VarN (S Z) `AppN` LamN (LamN (NeutralN (VarN Z)))))))))
test1 = Refl

fix : {ctx : Context} -> ctx :: Star |- Star -> ctx |- Star
fix m = Lam ((Lam (var 1 `App` (var 0 `App` var 0))) `App` (Lam (var 1 `App` (var 0 `App` var 0)))) `App` Lam m

two : {ctx : Context} -> ctx |- Star
two = sucSc $ sucSc zeroSc

four : {ctx : Context} -> ctx |- Star
four = sucSc . sucSc . sucSc $ sucSc zeroSc

plus : {ctx : Context} -> ctx |- Star
plus = fix (Lam . Lam $ caseSc (var 1) (var 0) (sucSc (var 3 `App` var 0 `App` var 1)))

test2 : fst (Untyped.eval 100 (Untyped.plus `App` Untyped.two `App` Untyped.two)) = fst (Untyped.eval 100 Untyped.four)
test2 = Refl

mult : {ctx : Context} -> ctx |- Star
mult = fix (Lam . Lam $ caseSc (var 1) zeroSc (plus `App` var 1 `App` (var 3 `App` var 0 `App` var 1)))

test3 : fst (Untyped.eval 100 (Untyped.mult `App` Untyped.two `App` Untyped.two)) = fst (Untyped.eval 100 Untyped.four)
test3 = Refl

public export
appLCong : {l, m : _} -> l -=>> l' -> l `App` m -=>> l' `App` m
appLCong Refl = Refl
appLCong (x `Trans` y) = IntroAppLeft x `Trans` appLCong y

public export
appRCong : {l, m : _} -> m -=>> m' -> l `App` m -=>> l `App` m'
appRCong Refl = Refl
appRCong (x `Trans` y) = IntroAppRight x `Trans` appRCong y

public export
lamCong : m -=>> m' -> Lam m -=>> Lam m'
lamCong Refl = Refl
lamCong (x `Trans` y) = IntroLam x `Trans` lamCong y

public export
(>>) : l -=>> m -> m -=>> n -> l -=>> n
(>>) Refl x = x
(>>) (y `Trans` z) x = y `Trans` z >> x

-- Monoid (m -=>> n) where

