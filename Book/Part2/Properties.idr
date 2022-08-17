module Book.Part2.Properties
import Decidable.Equality
import Book.Part2.Lambda
import Book.Part1.Isomorphism
%default total

public export
valuesDontReduce : Value m -> Not (ReduceStep m n)
valuesDontReduce VLam (IntroAppLeft x) impossible
valuesDontReduce VLam (IntroAppRight x y) impossible
valuesDontReduce VLam (IntroSuc x) impossible
valuesDontReduce VLam (IntroCase x) impossible
valuesDontReduce VLam (BetaLam x) impossible
valuesDontReduce VLam BetaZero impossible
valuesDontReduce VLam (BetaSuc _) impossible
valuesDontReduce VLam BetaMu impossible
valuesDontReduce VZero (IntroAppLeft x) impossible
valuesDontReduce VZero (IntroAppRight x y) impossible
valuesDontReduce VZero (IntroSuc x) impossible
valuesDontReduce VZero (IntroCase x) impossible
valuesDontReduce VZero (BetaLam x) impossible
valuesDontReduce VZero BetaZero impossible
valuesDontReduce VZero (BetaSuc _) impossible
valuesDontReduce VZero BetaMu impossible
valuesDontReduce (VSuc x) (IntroSuc y) = valuesDontReduce x y

public export
reduceNotValue : ReduceStep m n -> Not (Value m)
reduceNotValue x y = valuesDontReduce y x

data Canonical : Term -> LambdaType -> Type where
  CanonicalLam : TypeOf (Assigned Empty x a) n b -> Canonical (Lam x n) (Arr a b)
  CanonicalZero : Canonical Zero LambdaNat
  CanonicalSuc : Canonical v LambdaNat -> Canonical (Suc v) LambdaNat

canonical : TypeOf Empty v a -> Value v -> Canonical v a
canonical (Axiom _) VLam impossible
canonical (Axiom _) VZero impossible
canonical (Axiom _) (VSuc y) impossible
canonical (IntroArr x) VLam = CanonicalLam x
canonical (ElimArr _ _) VLam impossible
canonical (ElimArr _ _) VZero impossible
canonical (ElimArr _ _) (VSuc y) impossible
canonical IntroNZ VZero = CanonicalZero
canonical (IntroNSuc x) (VSuc y) = CanonicalSuc (canonical x y)
canonical (IntroNCase _ _ _) VLam impossible
canonical (IntroNCase _ _ _) VZero impossible
canonical (IntroNCase _ _ _) (VSuc y) impossible
canonical (IntroMu _) VLam impossible
canonical (IntroMu _) VZero impossible
canonical (IntroMu _) (VSuc y) impossible

value : Canonical v a -> Value v
value (CanonicalLam x) = VLam
value CanonicalZero = VZero
value (CanonicalSuc x) = VSuc (value x)

typed : Canonical v a -> TypeOf Empty v a
typed (CanonicalLam x) = IntroArr x
typed CanonicalZero = IntroNZ
typed (CanonicalSuc x) = IntroNSuc (typed x)

public export
data Progress : Term -> Type where
  Step : {n : Term} -> ReduceStep m n -> Progress m
  Done : Value m -> Progress m

public export
progress : {m : Term} -> TypeOf Empty m a -> Progress m
progress (Axiom Z) impossible
progress (Axiom (S f x)) impossible
progress (IntroArr _) = Done VLam
progress (ElimArr x y) with (progress x)
  progress (ElimArr x y) | (Step z) = Step (IntroAppLeft z)
  progress (ElimArr x y) | (Done z) with (progress y)
    progress (ElimArr x y) | (Done z) | (Step w) = Step (IntroAppRight z w)
    progress (ElimArr x y) | (Done z) | (Done w) with (canonical x z)
      progress (ElimArr x y) | (Done z) | (Done w) | (CanonicalLam v) = Step (BetaLam w)
progress IntroNZ = Done VZero
progress (IntroNSuc x) with (progress x)
  progress (IntroNSuc x) | (Step y) = Step (IntroSuc y)
  progress (IntroNSuc x) | (Done y) = Done (VSuc y)
progress (IntroNCase x y z) with (progress x)
  progress (IntroNCase x y z) | (Step w) = Step (IntroCase w)
  progress (IntroNCase x y z) | (Done w) with (canonical x w)
    progress (IntroNCase x y z) | (Done w) | CanonicalZero = Step BetaZero
    progress (IntroNCase x y z) | (Done w) | (CanonicalSuc v) = Step (BetaSuc $ value v)
progress (IntroMu x) = Step BetaMu


progressToEither : Progress m -> Either (Value m) (n : Term ** ReduceStep m n)
progressToEither (Step {n} x) = Right (MkDPair n x)
progressToEither (Done x) = Left x

eitherToProgress : Either (Value m) (DPair Term (\ n => ReduceStep m n)) -> Progress m
eitherToProgress (Left x) = Done x
eitherToProgress (Right (MkDPair _ x)) = Step x

fromToProgress : (x : Progress m) -> eitherToProgress (progressToEither x) = x
fromToProgress (Step x) = Refl
fromToProgress (Done x) = Refl

toFromProgress : (y : Either (Value m) (n : Term ** ReduceStep m n)) -> progressToEither (eitherToProgress y) = y
toFromProgress (Left x) = Refl
toFromProgress (Right (MkDPair fst snd)) = Refl

progressEither : Iso (Progress m) (Either (Value m) (DPair Term (\ n => ReduceStep m n)))
progressEither = MkIso progressToEither eitherToProgress fromToProgress toFromProgress

progress' : {m : Term} -> TypeOf Empty m a -> Either (Value m) (n : Term ** ReduceStep m n)
progress' (Axiom Z) impossible
progress' (Axiom (S f x)) impossible
progress' (IntroArr _) = Left VLam
progress' (ElimArr x y) with (progress' x)
  progress' (ElimArr x y) | (Right (MkDPair fst snd)) = Right (MkDPair (App fst _) (IntroAppLeft snd))
  progress' (ElimArr x y) | (Left z) with (progress' y)
    progress' (ElimArr x y) | (Left z) | (Right (MkDPair fst snd)) = Right (MkDPair (App _ fst) (IntroAppRight z snd))
    progress' (ElimArr x y) | (Left z) | (Left w) with (canonical x z)
      progress' (ElimArr x y) | (Left z) | (Left w) | (CanonicalLam v) = Right (MkDPair _ (BetaLam w))
progress' IntroNZ = Left VZero
progress' (IntroNSuc x) with (progress' x)
  progress' (IntroNSuc x) | (Left y) = Left (VSuc y)
  progress' (IntroNSuc x) | (Right (MkDPair fst snd)) = Right (MkDPair (Suc fst) (IntroSuc snd))
progress' (IntroNCase x y z) with (progress' x)
  progress' (IntroNCase x y z) | (Right (MkDPair fst snd)) = Right (MkDPair (Case fst _ _ _) (IntroCase snd))
  progress' (IntroNCase x y z) | (Left w) with (canonical x w)
    progress' (IntroNCase x y z) | (Left w) | CanonicalZero = Right (MkDPair _ BetaZero)
    progress' (IntroNCase x y z) | (Left w) | (CanonicalSuc v) = Right (MkDPair _ (BetaSuc $ value v))
progress' (IntroMu x) = Right (MkDPair _ BetaMu)

decValue : {m : Term} -> TypeOf Empty m a -> Dec (Value m)
decValue x with (progress x)
  decValue x | (Step y) = No (reduceNotValue y)
  decValue x | (Done y) = Yes y


ext
  : ({x : Id} -> {0 a : LambdaType} -> Lookup ctx x a -> Lookup ctx' x a)
  -> {x : Id} -> {0 a : LambdaType} -> Lookup (Assigned ctx y b) x a -> Lookup (Assigned ctx' y b) x a
ext f Z = Z
ext f (S g z) = S g (f z)

rename
  : ({x : Id} -> {0 a : LambdaType} -> Lookup ctx x a -> Lookup ctx' x a)
  -> {m : Term} -> {0 a : LambdaType} -> TypeOf ctx m a -> TypeOf ctx' m a
rename f (Axiom x) = Axiom (f x)
rename f (IntroArr x) = IntroArr (rename (ext f) x)
rename f (ElimArr x y) = ElimArr (rename f x) (rename f y)
rename f IntroNZ = IntroNZ
rename f (IntroNSuc x) = IntroNSuc (rename f x)
rename f (IntroNCase x y z) = IntroNCase (rename f x) (rename f y) (rename (ext f) z)
rename f (IntroMu x) = IntroMu (rename (ext f) x)

public export
weaken : {m : Term} -> TypeOf Empty m a -> TypeOf ctx m a
weaken = rename f
  where
    f : Lookup Empty y b -> Lookup ctx y b
    f x impossible


public export
drop :  {m : Term} -> TypeOf (Assigned (Assigned ctx x a) x b) m c
     -> TypeOf (Assigned ctx x b) m c
drop = rename lemma
  where 
    lemma : Lookup (Assigned (Assigned ctx x a) x b) y z -> Lookup (Assigned ctx x b) y z
    lemma Z = Z
    lemma (S imp Z) = absurd (imp Refl)
    lemma (S f (S g x)) = S g x

public export
swap : {m : Term}
    -> Not (x = y)
    -> TypeOf (Assigned (Assigned ctx y a) x b) m c
    -> TypeOf (Assigned (Assigned ctx x b) y a) m c
swap neq = rename f
  where f : Lookup (Assigned (Assigned ctx y a) x b) k d
         -> Lookup (Assigned (Assigned ctx x b) y a) k d
        f Z = S neq Z
        f (S _ Z) = Z
        f (S neqx (S neqy z)) = S neqy (S neqx z)

public export
subst : {m, v : Term} -> {x : Id} -> TypeOf Empty v a -> TypeOf (Assigned ctx x a) m b -> TypeOf ctx (replace m x v) b
subst {m = (Var x)} {x} y (Axiom Z) with (decEq x x)
  subst {m = (Var x)} {x = x} y (Axiom Z) | (Yes Refl) = weaken y
  subst {m = (Var x)} {x = x} y (Axiom Z) | (No contra) = absurd $ contra Refl
subst {m = (Var z)} {x} y (Axiom (S f a)) with (decEq z x)
  subst {m = (Var z)} {x = z} y (Axiom (S f a)) | (Yes Refl) = absurd $ f Refl
  subst {m = (Var z)} {x = x} y (Axiom (S f a)) | (No contra) = Axiom a
subst {m = (Lam x' n)} {x} y (IntroArr z) with (decEq x' x)
  subst {m = (Lam x' n)} {x = x'} y (IntroArr z) | (Yes Refl) = IntroArr (drop z)
  subst {m = (Lam x' n)} {x = x} y (IntroArr z) | (No contra) = IntroArr (subst y (swap contra z))
subst {m = (App left middle)} y (ElimArr z w) = ElimArr (subst y z) (subst y w)
subst {m = Zero} _ IntroNZ = IntroNZ
subst {m = (Suc m)} y (IntroNSuc z) = IntroNSuc (subst y z)
subst {m = (Case left middle x' right)} {x} y (IntroNCase z w s) with (decEq x' x)
  subst {m = (Case left middle x' right)} {x = x'} y (IntroNCase z w s) | (Yes Refl) = IntroNCase (subst y z) (subst y w) (drop s)
  subst {m = (Case left middle x' right)} {x = x} y (IntroNCase z w s) | (No contra) = IntroNCase (subst y z) (subst y w) (subst y (swap contra s))
subst {m = (Mu x' middle)} {x} y (IntroMu z) with (decEq x' x)
  subst {m = (Mu x' middle)} {x = x'} y (IntroMu z) | (Yes Refl) = IntroMu (drop z)
  subst {m = (Mu x' middle)} {x = x} y (IntroMu z) | (No contra) = IntroMu (subst y (swap contra z))

-- The order of the clauses matters, the with clauses are necessary, and there's probably a bunch of issues in idris2 to be reported here
public export
preserve : {m, n : Term} -> TypeOf Empty m a -> ReduceStep m n -> TypeOf Empty n a
preserve (IntroNCase x' z w) (BetaSuc y) with (x')
  preserve (IntroNCase x' z w) (BetaSuc y) | (IntroNSuc x) = subst x w
preserve (ElimArr x z) (IntroAppLeft y) = ElimArr (preserve x y) z
preserve (ElimArr x w) (IntroAppRight y z) = ElimArr x (preserve w z)
preserve (ElimArr x' z) (BetaLam y) with (x')
  preserve (ElimArr x' z) (BetaLam y) | (IntroArr x) = subst z x
preserve (IntroNSuc x) (IntroSuc y) = IntroNSuc (preserve x y)
preserve (IntroNSuc x) (BetaLam _) impossible
preserve (IntroNSuc x) (BetaSuc _) impossible
preserve (IntroNCase x z w) (IntroCase y) = IntroNCase (preserve x y) z w
preserve (IntroNCase x y z) BetaZero = y
preserve (IntroNCase x y z) (BetaLam _) impossible
preserve (Axiom x) y impossible
preserve (IntroArr x) y impossible
preserve IntroNZ y impossible
preserve (IntroMu x) y = ?h2
