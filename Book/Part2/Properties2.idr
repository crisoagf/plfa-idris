module Book.Part2.Properties2
import Decidable.Equality
import Book.Part2.Properties
import Book.Part2.Lambda
import Book.Part1.Isomorphism
%default total

-- Split into two files so that totality checking doesn't take forever

data ReducesIn : Nat -> Term -> Term -> Type where
  Finished : Value m -> ReducesIn (S k) m m
  OutOfGas : ReducesIn 0 m m
  Step : ReduceStep m n -> ReducesIn k n o -> ReducesIn (S k) m o


eval : {m : Term} -> (k : Nat) -> TypeOf Empty m a -> (n : Term ** ReducesIn k m n)
eval 0 x = (_ ** OutOfGas)
eval (S k) x with (progress x)
  eval (S k) x | (Done y) = MkDPair m (Finished y)
  eval (S k) x | (Step y) with (eval k (preserve x y))
    eval (S k) x | (Step y) | (MkDPair fst snd) = MkDPair fst (Step y snd)


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
  unstuck x y | (Step z) = fst y z
  unstuck x y | (Done z) = snd y z

preserves : {m, n : Term} -> TypeOf Empty m a -> Reduce m n -> TypeOf Empty n a
preserves x Refl = x
preserves x (Trans m y z) = preserves (preserve x y) z

wttdgs : {m, n : Term} -> TypeOf Empty m a -> Reduce m n -> Not (Stuck n)
wttdgs x y = unstuck (preserves x y)

valueDet : (x, y : Value m) -> x = y
valueDet VLam VLam = Refl
valueDet VZero VZero = Refl
valueDet (VSuc x) (VSuc y) = rewrite valueDet x y in Refl

det' : (s : ReduceStep m m') -> (s' : ReduceStep m m'') -> (m' = m'', s = s')
det' (IntroAppLeft x) (IntroAppLeft y) with (det' x y)
  det' (IntroAppLeft x) (IntroAppLeft x) | (Refl, Refl) = (Refl, Refl)
det' (IntroAppLeft x) (IntroAppRight y z) = absurd $ reduceNotValue x y
det' (IntroAppLeft x) (BetaLam y) = absurd $ reduceNotValue x VLam
det' (IntroAppRight x z) (IntroAppLeft y) = absurd $ valuesDontReduce x y
det' (IntroAppRight x z) (IntroAppRight y w) with (det' z w)
  det' (IntroAppRight x z) (IntroAppRight y z) | (Refl, Refl) = rewrite valueDet x y in (Refl, Refl)
det' (IntroAppRight x z) (BetaLam y) = absurd $ reduceNotValue z y
det' (IntroSuc x) (IntroSuc y) with (det' x y)
  det' (IntroSuc x) (IntroSuc x) | (Refl, Refl) = (Refl, Refl)
det' (IntroCase x) (IntroCase y) with (det' x y)
  det' (IntroCase x) (IntroCase x) | (Refl, Refl) = (Refl, Refl)
det' (IntroCase x) BetaZero = absurd $ reduceNotValue x VZero
det' (IntroCase x) (BetaSuc y) = absurd $ reduceNotValue x (VSuc y)
det' (BetaLam x) (IntroAppLeft y) = absurd $ valuesDontReduce VLam y
det' (BetaLam x) (IntroAppRight y z) = absurd $ valuesDontReduce x z
det' (BetaLam x) (BetaLam y) = rewrite valueDet x y in (Refl, Refl)
det' BetaZero (IntroCase x) = absurd $ valuesDontReduce VZero x
det' BetaZero BetaZero = (Refl, Refl)
det' (BetaSuc x) (IntroCase y) = absurd $ valuesDontReduce (VSuc x) y
det' (BetaSuc x) (BetaSuc y) = rewrite valueDet x y in (Refl, Refl)
det' BetaMu (IntroAppLeft x) impossible
det' BetaMu (IntroAppRight x y) impossible
det' BetaMu (IntroSuc x) impossible
det' BetaMu (IntroCase x) impossible
det' BetaMu (BetaLam x) impossible
det' BetaMu BetaZero impossible
det' BetaMu (BetaSuc x) impossible
det' BetaMu BetaMu = (Refl, Refl)

det : (ReduceStep m m') -> (ReduceStep m m'') -> m' = m''
det x y = fst (det' x y)

-- Not compiling, I am not gonna fight the compiler
-- evTwo : eval 100 (ElimArr (ElimArr Lambda.typeOfChurchTwo Lambda.typeOfSuc) IntroNZ) =
--   MkDPair (Suc (Suc Zero))
--     (Step (IntroAppLeft (BetaLam VLam))
--     (Step (BetaLam VZero)
--     (Step (IntroAppRight VLam (BetaLam VZero))
--     (Step (BetaLam (VSuc VZero))
--     (Finished (VSuc (VSuc VZero)))
--     ))))
-- evTwo with (eval 100 (ElimArr (ElimArr Lambda.typeOfChurchTwo Lambda.typeOfSuc) IntroNZ))
--  evTwo | ((Var x) ** (Step y z)) with (y)
--    evTwo | ((Var x) ** (Step y z)) | (IntroAppLeft w) = ?evTwo_rhs_1
--    evTwo | ((Var x) ** (Step y z)) | (IntroAppRight w v) = ?evTwo_rhs_2
--  evTwo | ((Lam x y) ** snd) = ?help_3
--  evTwo | ((App x y) ** snd) = ?help_4
--  evTwo | (Zero ** snd) = ?help_5
--  evTwo | ((Suc x) ** snd) = ?help_6
--  evTwo | ((Case x y z w) ** snd) = ?help_7
--  evTwo | ((Mu x y) ** snd) = ?help_8

