module Properties2
import Decidable.Equality
import Properties
import Lambda
import Isomorphism
%default total

data ReducesIn : Nat -> Term -> Term -> Type where
  Finished : Value m -> ReducesIn (S k) m m
  OutOfGas : ReducesIn 0 m m
  Step : ReduceStep m n -> ReducesIn k n o -> ReducesIn (S k) m o


eval : {m : Term} -> (k : Nat) -> TypeOf Empty m a -> (n : Term ** ReducesIn k m n)
eval 0 x = (_ ** OutOfGas)
eval (S k) x with (progress x)
  eval (S k) x | (done y) = MkDPair m (Finished y)
  eval (S k) x | (step y) with (eval k (preserve x y))
    eval (S k) x | (step y) | (MkDPair fst snd) = MkDPair fst (Step y snd)


evTwo : eval 100 (ElimArr (ElimArr Lambda.typeOfChurchTwo Lambda.typeOfSuc) IntroNZ) =
  MkDPair (Suc (Suc Zero))
    (Step (IntroAppLeft (BetaLam VLam))
    (Step (BetaLam VZero)
    (Step (IntroAppRight VLam (BetaLam VZero))
    (Step (BetaLam (VSuc VZero))
    (Finished (VSuc (VSuc VZero)))
    ))))
evTwo with (eval 100 (ElimArr (ElimArr Lambda.typeOfChurchTwo Lambda.typeOfSuc) IntroNZ))
 evTwo | MkDPair (Suc (Suc Zero)) (Step (IntroAppLeft (BetaLam VLam)) (Step (BetaLam VZero) (Step (IntroAppRight VLam (BetaLam VZero)) (Step (BetaLam (VSuc VZero)) (Finished (VSuc (VSuc VZero))))))) = Refl
 evTwo | (MkDPair (Var _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (Var _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (Var _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (Var _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (Var _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (Var _) (Step BetaMu _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (Lam _ _) (Step BetaMu _)) impossible
 evTwo | (MkDPair (App (App (Lam _ (Lam _ (App (Var _) (App (Var _) (Var _))))) (Lam _ (Suc (Var _)))) Zero) (Finished VLam)) impossible
 evTwo | (MkDPair (App (App (Lam _ (Lam _ (App (Var _) (App (Var _) (Var _))))) (Lam _ (Suc (Var _)))) Zero) (Finished VZero)) impossible
 evTwo | (MkDPair (App (App (Lam _ (Lam _ (App (Var _) (App (Var _) (Var _))))) (Lam _ (Suc (Var _)))) Zero) (Finished (VSuc x))) impossible
 evTwo | (MkDPair (App _ _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (App _ _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (App _ _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (App _ _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (App _ _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (App _ _) (Step BetaMu _)) impossible
 evTwo | (MkDPair Zero (Step (IntroSuc x) _)) impossible
 evTwo | (MkDPair Zero (Step (IntroCase x) _)) impossible
 evTwo | (MkDPair Zero (Step (BetaLam x) _)) impossible
 evTwo | (MkDPair Zero (Step BetaZero _)) impossible
 evTwo | (MkDPair Zero (Step (BetaSuc x) _)) impossible
 evTwo | (MkDPair Zero (Step BetaMu _)) impossible
 evTwo | (MkDPair (Suc _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (Suc _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (Suc _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (Suc _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (Suc _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (Suc _) (Step BetaMu _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (Case _ _ _ _) (Step BetaMu _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step (IntroSuc y) _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step (IntroCase y) _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step (BetaLam y) _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step BetaZero _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step (BetaSuc y) _)) impossible
 evTwo | (MkDPair (Mu _ _) (Step BetaMu _)) impossible

subject_expansion_counterexample1 : (n : Term ** m : Term ** a : LambdaType **
  (Reduce m n, TypeOf Empty n a, Not (TypeOf Empty m a)))
subject_expansion_counterexample1 =
  (Zero **
  (Case Zero Zero "x" (Var "y") **
  (LambdaNat **
    (Trans (Case Zero Zero "x" (Var "y")) BetaZero Refl, IntroNZ, notTyped)
  )))
  where
    notTyped : TypeOf Empty (Case Zero Zero "x" (Var "y")) LambdaNat -> Void
    notTyped (IntroNCase IntroNZ IntroNZ (Axiom (S _ Z))) impossible
    notTyped (IntroNCase IntroNZ IntroNZ (Axiom (S _ (S g x)))) impossible

subject_expansion_counterexample2 : (n : Term ** m : Term ** a : LambdaType **
  (Reduce m n, TypeOf Empty n a, Not (TypeOf Empty m a)))
subject_expansion_counterexample2 =
  (Zero **
  (App (App (Lam "x" (Lam "y" (Var "x"))) Zero) (Suc (Lam "z" (Var "z"))) **
  (LambdaNat **
    (Trans (App (App (Lam "x" (Lam "y" (Var "x"))) Zero) (Suc (Lam "z" (Var "z")))) (IntroAppLeft (BetaLam VZero))
    (Trans (App (Lam "y" Zero) (Suc (Lam "z" (Var "z")))) (BetaLam (VSuc VLam)) Refl), IntroNZ, h3)
  )))
  where
    h3 : TypeOf Empty (App (App (Lam "x" (Lam "y" (Var "x"))) Zero) (Suc (Lam "z" (Var "z")))) LambdaNat -> Void
    h3 (ElimArr _ (IntroNSuc (Axiom y))) impossible
    h3 (ElimArr _ (IntroNSuc (IntroArr y))) impossible
    h3 (ElimArr _ (IntroNSuc (ElimArr y z))) impossible
    h3 (ElimArr _ (IntroNSuc IntroNZ)) impossible
    h3 (ElimArr _ (IntroNSuc (IntroNSuc y))) impossible
    h3 (ElimArr _ (IntroNSuc (IntroNCase y z w))) impossible
    h3 (ElimArr _ (IntroNSuc (IntroMu y))) impossible

Normal : Term -> Type
Normal m = {n : Term} -> Not (ReduceStep m n)

Stuck : Term -> Type
Stuck m = (Normal m , Not (Value m))

unstuck : {m : Term} -> TypeOf Empty m a -> Not (Stuck m)
unstuck x y with (progress x)
  unstuck x y | (step z) = fst y z
  unstuck x y | (done z) = snd y z

preserves : {m, n : Term} -> TypeOf Empty m a -> Reduce m n -> TypeOf Empty n a
preserves x Refl = x
preserves x (Trans m y z) = preserves (preserve x y) z

wttdgs : {m, n : Term} -> TypeOf Empty m a -> Reduce m n -> Not (Stuck n)
wttdgs x y = unstuck (preserves x y)

det : ReduceStep m m' -> ReduceStep m m'' -> m' = m''
det (IntroAppLeft x) (IntroAppLeft y) = rewrite det x y in Refl
det (IntroAppLeft x) (IntroAppRight y z) = absurd $ reduceNotValue x y
det (IntroAppLeft x) (BetaLam y) = absurd $ reduceNotValue x VLam
det (IntroAppRight x z) (IntroAppLeft y) = absurd $ valuesDontReduce x y
det (IntroAppRight x z) (IntroAppRight y w) = rewrite det z w in Refl
det (IntroAppRight x z) (BetaLam y) = absurd $ reduceNotValue z y
det (IntroSuc x) (IntroSuc y) = rewrite det x y in Refl
det (IntroCase x) (IntroCase y) = rewrite det x y in Refl
det (IntroCase x) BetaZero = absurd $ reduceNotValue x VZero
det (IntroCase x) (BetaSuc y) = absurd $ reduceNotValue x (VSuc y)
det (BetaLam x) (IntroAppLeft y) = absurd $ valuesDontReduce VLam y
det (BetaLam x) (IntroAppRight y z) = absurd $ valuesDontReduce x z
det (BetaLam x) (BetaLam y) = Refl
det BetaZero (IntroCase x) = absurd $ valuesDontReduce VZero x
det BetaZero BetaZero = Refl
det (BetaSuc x) (IntroCase y) = absurd $ valuesDontReduce (VSuc x) y
det (BetaSuc x) (BetaSuc y) = Refl
det BetaMu (IntroAppLeft x) impossible
det BetaMu (IntroAppRight x y) impossible
det BetaMu (IntroSuc x) impossible
det BetaMu (IntroCase x) impossible
det BetaMu (BetaLam x) impossible
det BetaMu BetaZero impossible
det BetaMu (BetaSuc x) impossible
det BetaMu BetaMu = Refl

