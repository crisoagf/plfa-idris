module Quantifiers
import Isomorphism
import Relations
import Data.Nat
import Naturals
import Induction

public export
Extensionality : Type
Extensionality = {a : Type} -> {b : a -> Type} -> {f, g : (x : a) -> b x} -> ((x : a) -> (f x = g x)) -> f = g

etaTimes : (w : (a, b)) -> (fst w, snd w) = w
etaTimes (_, _) = Refl

forallDistribTimes : {a : Type} -> Extensionality -> {b, c : a -> Type} -> Iso ((x : a) -> (b x, c x)) ((x : a) -> b x, (x : a) -> c x)
forallDistribTimes ext = MkIso fpToPf pfToFp fpId pfId
  where
    fpToPf : {0 b, c : a -> Type} -> ((x : a) -> (b x, c x)) -> ((x : a) -> b x, (x : a) -> c x)
    fpToPf f = (\ x => fst (f x), \ x => snd (f x))
    pfToFp : {0 b, c : a -> Type} -> ((x : a) -> b x, (x : a) -> c x) -> (x : a) -> (b x, c x)
    pfToFp (y, z) x = (y x, z x)
    fpId : (f : ((x : a) -> (b x, c x))) -> pfToFp (\x => fst (f x), \x => snd (f x)) = f
    fpId f = ext (\ x => etaTimes (f x))
    pfId : (y : ((x : a) -> b x, (x : a) -> c x)) -> (\x => fst (pfToFp y x), \x => snd (pfToFp y x)) = y
    pfId (z, y) = the ((\x => z x, \x => y x) = (z, y)) Refl

eitherForallToForallEither : {0 b, c : a -> Type} -> Either ((x : a) -> b x) ((x : a) -> c x) -> (x : a) -> Either (b x) (c x)
eitherForallToForallEither (Left y) x = Left (y x)
eitherForallToForallEither (Right y) x = Right (y x)

data Sigma : (0 a : Type) -> (0 b : a -> Type) -> Type where
  MkSigma : (x : a) -> b x -> Sigma a b

sigmaElim : ((x : a) -> b x -> c) -> Sigma a b -> c
sigmaElim f (MkSigma x y) = f x y

forallSigmaCurrying : {a, c : Type} -> {b : a -> Type} -> Extensionality -> Iso ((x : a) -> b x -> c) (Sigma a b -> c)
forallSigmaCurrying ext = MkIso sigmaUncurry forallCurry sfId fsId
  where
    sigmaUncurry : ((x : a) -> b x -> c) -> Sigma a b -> c
    sigmaUncurry = sigmaElim
    forallCurry : (Sigma a b -> c) -> (x : a) -> b x -> c
    forallCurry f x y = f (MkSigma x y)
    sfId : (x : ((x : a) -> b x -> c)) -> forallCurry (sigmaElim x) = x
    sfId x = ext (\y => ext (\z => Refl))
    fsId : (y : (Sigma a b -> c)) -> sigmaElim (forallCurry y) = y
    fsId y = ext (\ (MkSigma x z) => Refl)

sigmaDistribEither : Iso (Sigma a (\ x => Either (b x) (c x))) (Either (Sigma a b) (Sigma a c))
sigmaDistribEither = MkIso sigmaEither eitherSigma seId esId
  where
    sigmaEither : Sigma a (\x => Either (b x) (c x)) -> Either (Sigma a b) (Sigma a c)
    sigmaEither (MkSigma x (Left y)) = Left (MkSigma x y)
    sigmaEither (MkSigma x (Right y)) = Right (MkSigma x y)
    eitherSigma : Either (Sigma a b) (Sigma a c) -> Sigma a (\x => Either (b x) (c x))
    eitherSigma (Left (MkSigma x y)) = MkSigma x (Left y)
    eitherSigma (Right (MkSigma x y)) = MkSigma x (Right y)
    seId : (x : Sigma a (\x => Either (b x) (c x))) -> eitherSigma (sigmaEither x) = x
    seId (MkSigma x (Left y)) = Refl
    seId (MkSigma x (Right y)) = Refl
    esId : (y : Either (Sigma a b) (Sigma a c)) -> sigmaEither (eitherSigma y) = y
    esId (Left (MkSigma x y)) = Refl
    esId (Right (MkSigma x y)) = Refl

sigmaTimesTraverse : Sigma a (\ x => (b x, c x)) -> (Sigma a b, Sigma a c)
sigmaTimesTraverse (MkSigma x (y, z)) = (MkSigma x y, MkSigma x z)

CounterExampleB : Bool -> Type
CounterExampleB True = ()
CounterExampleB False = Void

CounterExampleC : Bool -> Type
CounterExampleC True = Void
CounterExampleC False = ()

timesSigmaCounterexample : Not ({a : Type} -> {b, c : a -> Type}
  -> (Sigma a b, Sigma a c) -> Sigma a (\ x => (b x, c x)))
timesSigmaCounterexample f = nullifyCounterExample $ f (MkSigma True (), MkSigma False ())
  where
    nullifyCounterExample : Sigma Bool (\ x => (CounterExampleB x, CounterExampleC x)) -> Void
    nullifyCounterExample (MkSigma True (x, y)) = y
    nullifyCounterExample (MkSigma False (x, y)) = x

evenExists : Even n -> Sigma Nat (\ m => m * 2 = n)
evenExists Zero = MkSigma 0 Refl
evenExists (EvenS (OddS x)) with (evenExists x)
  evenExists (EvenS (OddS x)) | (MkSigma y z) = MkSigma (S y) (cong (S . S) z)

oddExists : Odd n -> Sigma Nat (\ m => 1 + m * 2 = n)
oddExists (OddS x) with (evenExists x)
  oddExists (OddS x) | (MkSigma y z) = MkSigma y (cong S z)

existsEven : Sigma Nat (\ m => m * 2 = n) -> Even n
existsEven (MkSigma 0 Refl) = Zero
existsEven (MkSigma (S k) Refl) = EvenS (OddS (existsEven (MkSigma k Refl)))

existsOdd : Sigma Nat (\ m => 1 + m * 2 = n) -> Odd n
existsOdd (MkSigma 0 Refl) = OddS Zero
existsOdd (MkSigma (S k) Refl) = OddS (EvenS (existsOdd (MkSigma k Refl)))

existsLTE : {z : Nat} -> LTE y z -> Sigma Nat (\ x => x + y = z)
existsLTE LTEZero = MkSigma z (plusZeroRightNeutral z)
existsLTE (LTESucc x) with (existsLTE x)
  existsLTE (LTESucc x) | (MkSigma w v) = MkSigma w (sym (plusSuccRightSucc w _) `trans` cong S v)

notExistsForallNot : {a : Type} -> Extensionality -> {b : a -> Type} -> Iso (Not (Sigma a (\ x => b x))) ((x : a) -> Not (b x))
notExistsForallNot ext = MkIso generalize specialize gsId sgId
  where
    generalize : (Sigma a (\x => b x) -> Void) -> (x : a) -> b x -> Void
    generalize f x y = f (MkSigma x y)
    specialize : ((x : a) -> b x -> Void) -> Sigma a (\x => b x) -> Void
    specialize f (MkSigma x y) = f x y
    gsId : (x : (Sigma a (\x => b x) -> Void)) -> specialize (generalize x) = x
    gsId x = ext (\ (MkSigma x b) => Refl)
    sgId : (y : ((x : a) -> b x -> Void)) -> generalize (specialize y) = y
    sgId y = ext (\x => ext (\z => Refl))

existsNotToNotForall : {0 b : a -> Type} -> Sigma a (\ x => Not (b x)) -> Not ((x : a) -> b x)
existsNotToNotForall (MkSigma x y) f = y (f x)

notForallToNotExistsImpliesEM
  : ((a : Type) -> (b : a -> Type) -> Not ((x : a) -> b x) -> Sigma a (\ x => Not (b x)))
  -> (a : Type) -> Either a (Not a)
notForallToNotExistsImpliesEM f a
  = case f (Either a (Not a)) (\ _ => Void) doIt of
         (MkSigma x y) => x
  where doIt : (Either a (a -> Void) -> Void) -> Void
        doIt f = f $ Right $ \ a => f (Left a)

canonicalOne : (o, o' : One b) -> o = o'
canonicalOne OneEmpty OneEmpty = Refl
canonicalOne OneEmpty (OneI OneEmpty) impossible
canonicalOne OneEmpty (OneI (OneO x)) impossible
canonicalOne OneEmpty (OneI (OneI x)) impossible
canonicalOne (OneO x) (OneO y) = cong OneO (canonicalOne x y)
canonicalOne (OneI OneEmpty) OneEmpty impossible
canonicalOne (OneI (OneO x)) OneEmpty impossible
canonicalOne (OneI (OneI x)) OneEmpty impossible
canonicalOne (OneI x) (OneI y) = cong OneI (canonicalOne x y)

canonicalCan : (c, c' : Can b) -> c = c'
canonicalCan CanZero CanZero = Refl
canonicalCan CanZero (CanOne (OneO OneEmpty)) impossible
canonicalCan CanZero (CanOne (OneO (OneO x))) impossible
canonicalCan CanZero (CanOne (OneO (OneI x))) impossible
canonicalCan (CanOne (OneO OneEmpty)) CanZero impossible
canonicalCan (CanOne (OneO (OneO x))) CanZero impossible
canonicalCan (CanOne (OneO (OneI x))) CanZero impossible
canonicalCan (CanOne x) (CanOne y) = cong CanOne (canonicalOne x y)

canonicalCan' : (c : Can b) -> (c' : Can b') -> b = b' -> c = c'
canonicalCan' x y Refl = canonicalCan x y

congSigma : {x, x' : a} -> {b : a -> Type} -> {y : b x} -> {y' : b x'} -> x = x' -> b x = b x' -> y = y' -> MkSigma {b = b} x y = MkSigma x' y'
congSigma Refl Refl Refl = Refl

canIso : Iso Nat (Sigma Bin Can)
canIso = MkIso to' from' ftId tfId
  where
    to' : Nat -> Sigma Bin Can
    to' n = MkSigma (to n) (toCanonical n)
    from' : Sigma Bin Can -> Nat
    from' (MkSigma x y) = from x
    ftId : (x : Nat) -> from (to x) = x
    ftId x = fromToId x
    tfId : (y : Sigma Bin Can) -> MkSigma (to (from' y)) (toCanonical (from' y)) = y
    tfId (MkSigma x y) = congSigma
      (canonicalDef y)
      (cong Can (canonicalDef y))
      (canonicalCan' (toCanonical (from x)) y (canonicalDef y))

