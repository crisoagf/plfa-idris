module Relations
import Data.Nat
import Naturals

data LtE : Nat -> Nat -> Type where
  LtEZ : LtE 0 m
  LtES : LtE n m -> LtE (S n) (S m)

elimSLtES : LtE (S n) (S m) -> LtE n m
elimSLtES (LtES x) = x

elimMLtZ : LtE m 0 -> m = 0
elimMLtZ LtEZ = Refl

ltERefl : {1 n : Nat} -> LtE n n
ltERefl {n = 0} = LtEZ
ltERefl {n = (S k)} = LtES ltERefl

ltETrans : LtE m n -> LtE n p -> LtE m p
ltETrans LtEZ y = LtEZ
ltETrans (LtES x) (LtES y) = LtES (ltETrans x y)

ltEAntisym : LtE m n -> LtE n m -> m = n
ltEAntisym LtEZ LtEZ = Refl
ltEAntisym (LtES x) (LtES y) = cong S (ltEAntisym x y)

data Related : (t : Type) -> (t -> t -> Type) -> t -> t -> Type where
  Direct  : rel a b -> Related t rel a b
  Inverse : rel b a -> Related t rel a b

Total : (t : Type) -> (t -> t -> Type) -> Type
Total t rel = (a, b : t) -> Related t rel a b

ltETotal : Total Nat LtE
ltETotal 0 0 = Direct LtEZ
ltETotal 0 (S k) = Direct LtEZ
ltETotal (S k) 0 = Inverse LtEZ
ltETotal (S k) (S j) = case ltETotal k j of
                            (Direct x) => Direct (LtES x)
                            (Inverse x) => Inverse (LtES x)

plusLtEMonoRight : (1 p : Nat) -> LtE m n -> LtE (p + m) (p + n)
plusLtEMonoRight 0 x = x
plusLtEMonoRight (S k) x = LtES (plusLtEMonoRight k x)

plusLtEMonoLeft : {0 m, n : Nat} -> (p : Nat) -> LtE m n -> LtE (m + p) (n + p)
plusLtEMonoLeft {m} {n} p x = rewrite plusCommutative m p in
                              rewrite plusCommutative n p in plusLtEMonoRight p x

plusLtEMono : (n, p : Nat) -> LtE m n -> LtE p q -> LtE (m + p) (n + q)
plusLtEMono n p x y = plusLtEMonoLeft p x `ltETrans` plusLtEMonoRight n y

multLtEMonoRight : (m, n : Nat) -> (1 p : Nat) -> LtE m n -> LtE (p * m) (p * n)
multLtEMonoRight m n 0 x = LtEZ
multLtEMonoRight m n (S k) x = plusLtEMono n (mult k m) x (multLtEMonoRight m n k x)

multLtEMonoLeft : (m, n : Nat) -> (p : Nat) -> LtE m n -> LtE (m * p) (n * p)
multLtEMonoLeft m n p x = rewrite multCommutative m p in
                          rewrite multCommutative n p in multLtEMonoRight m n p x

multLtEMono : (m, n, p, q : Nat) -> LtE m n -> LtE p q -> LtE (m * p) (n * q)
multLtEMono m n p q x y = multLtEMonoLeft m n p x `ltETrans` multLtEMonoRight p q n y

data Lt : Nat -> Nat -> Type where
  LtZ : Lt Z (S m)
  LtS : Lt m n -> Lt (S m) (S n)

ltTrans : Lt m n -> Lt n p -> Lt m p
ltTrans LtZ (LtS x) = LtZ
ltTrans (LtS x) (LtS y) = LtS (ltTrans x y)

data TrichotomyPoint : (t : Type) -> (rel : t -> t -> Type) -> t -> t -> Type where
  TriRefl : TrichotomyPoint t rel a a
  TriDirect  : rel a b -> TrichotomyPoint t rel a b
  TriInverse : rel b a -> TrichotomyPoint t rel a b

Trichotomous : (t : Type) -> (t -> t -> Type) -> Type
Trichotomous t rel = (a, b : t) -> TrichotomyPoint t rel a b

ltTrichotomous : Trichotomous Nat Lt
ltTrichotomous 0 0 = TriRefl
ltTrichotomous 0 (S k) = TriDirect LtZ
ltTrichotomous (S k) 0 = TriInverse LtZ
ltTrichotomous (S k) (S j) = case ltTrichotomous k j of
                                  TriRefl => TriRefl
                                  (TriDirect x) => TriDirect (LtS x)
                                  (TriInverse x) => TriInverse (LtS x)

plusLtMonoRight : (1 p : Nat) -> Lt m n -> Lt (p + m) (p + n)
plusLtMonoRight 0 x = x
plusLtMonoRight (S k) x = LtS (plusLtMonoRight k x)

plusLtMonoLeft : {0 m, n : Nat} -> (p : Nat) -> Lt m n -> Lt (m + p) (n + p)
plusLtMonoLeft {m} {n} p x = rewrite plusCommutative m p in
                             rewrite plusCommutative n p in plusLtMonoRight p x

plusLtMono : (n, p : Nat) -> Lt m n -> Lt p q -> Lt (m + p) (n + q)
plusLtMono n p x y = plusLtMonoLeft p x `ltTrans` plusLtMonoRight n y

ltEToLt : LtE (S m) n -> Lt m n
ltEToLt (LtES LtEZ) = LtZ
ltEToLt (LtES (LtES x)) = LtS (ltEToLt (LtES x))

ltToLtE : Lt m n -> LtE (S m) n
ltToLtE LtZ = LtES LtEZ
ltToLtE (LtS x) = LtES (ltToLtE x)

dropAnS : LtE (S m) n -> LtE m n
dropAnS (LtES LtEZ) = LtEZ
dropAnS (LtES (LtES x)) = LtES (dropAnS (LtES x))

ltTrans' : Lt m n -> Lt n p -> Lt m p
ltTrans' x y = ltEToLt (LtES (dropAnS (ltToLtE x)) `ltETrans` ltToLtE y)

mutual
  public export
  data Even : Nat -> Type where
    Zero : Even Z
    EvenS : Odd n -> Even (S n)
  public export
  data Odd : Nat -> Type where
    OddS : Even n -> Odd (S n)

mutual
  evenPlusEven : Even n -> Even m -> Even (n + m)
  evenPlusEven Zero y = y
  evenPlusEven (EvenS x) y = EvenS (oddPlusEven x y)
  
  oddPlusEven : Odd n -> Even m -> Odd (n + m)
  oddPlusEven (OddS x) y = OddS (evenPlusEven x y)

mutual
  oddPlusOdd : Odd n -> Odd m -> Even (n + m)
  oddPlusOdd (OddS x) y = EvenS (evenPlusOdd x y)
  
  evenPlusOdd : Even n -> Odd m -> Odd (n + m)
  evenPlusOdd Zero y = y
  evenPlusOdd (EvenS x) y = OddS (oddPlusOdd x y)

public export
data One : Bin -> Type where
  OneEmpty : One (I Empty)
  OneO : One b -> One (O b)
  OneI : One b -> One (I b)

public export
data Can : Bin -> Type where
  CanZero : Can (O Empty)
  CanOne : One b -> Can b

incOneCompat : One b -> One (inc b)
incOneCompat OneEmpty = OneO OneEmpty
incOneCompat (OneO x) = OneI x
incOneCompat (OneI x) = OneO (incOneCompat x)

incCanCompat : Can b -> Can (inc b)
incCanCompat CanZero = CanOne OneEmpty
incCanCompat (CanOne x) = CanOne (incOneCompat x)

export
toCanonical : (1 n : Nat) -> Can (to n)
toCanonical 0 = CanZero
toCanonical (S k) = incCanCompat (toCanonical k)

binPlus : (b, c : Bin) -> Bin
binPlus Empty c = c
binPlus b Empty = b
binPlus (O x) (O y) = O (binPlus x y)
binPlus (O x) (I y) = I (binPlus x y)
binPlus (I x) (O y) = I (binPlus x y)
binPlus (I x) (I y) = O (inc (binPlus x y))

emptyBinPlusLeftId : (1 b : Bin) -> binPlus b Empty = b
emptyBinPlusLeftId Empty = Refl
emptyBinPlusLeftId (O x) = Refl
emptyBinPlusLeftId (I x) = Refl

zBinPlusLeftId : {b : Bin} -> (_ : Can b) -> binPlus b (O Empty) = b
zBinPlusLeftId CanZero = Refl
zBinPlusLeftId (CanOne x) = case x of
  OneEmpty => Refl
  (OneO x) => cong O (emptyBinPlusLeftId _)
  (OneI x) => cong I (emptyBinPlusLeftId _)

zBinPlusRightId : (_ : Can b) -> binPlus (O Empty) b = b
zBinPlusRightId CanZero = Refl
zBinPlusRightId (CanOne OneEmpty) = Refl
zBinPlusRightId (CanOne (OneO x)) = Refl
zBinPlusRightId (CanOne (OneI x)) = Refl

binPlusOneCompat : {b : Bin} -> One b -> One c -> One (binPlus b c)
binPlusOneCompat OneEmpty OneEmpty = OneO OneEmpty
binPlusOneCompat OneEmpty (OneO x) = OneI x
binPlusOneCompat OneEmpty (OneI x) = OneO (incOneCompat x)
binPlusOneCompat {b = O b} (OneO x) OneEmpty = rewrite emptyBinPlusLeftId b in OneI x
binPlusOneCompat {b = I b} (OneI x) OneEmpty = rewrite emptyBinPlusLeftId b in OneO (incOneCompat x)
binPlusOneCompat (OneO x) (OneO y) = OneO (binPlusOneCompat x y)
binPlusOneCompat (OneO x) (OneI y) = OneI (binPlusOneCompat x y)
binPlusOneCompat (OneI x) (OneO y) = OneI (binPlusOneCompat x y)
binPlusOneCompat (OneI x) (OneI y) = OneO (incOneCompat (binPlusOneCompat x y))

binPlusCanCompat : {b : Bin} -> Can b -> Can c -> Can (binPlus b c)
binPlusCanCompat CanZero    CanZero = CanZero
binPlusCanCompat CanZero    (CanOne OneEmpty) = CanOne OneEmpty
binPlusCanCompat CanZero    (CanOne (OneO x)) = CanOne (OneO x)
binPlusCanCompat CanZero    (CanOne (OneI x)) = CanOne (OneI x)
binPlusCanCompat x          CanZero = rewrite zBinPlusLeftId x in x
binPlusCanCompat (CanOne x) (CanOne y) = CanOne (binPlusOneCompat x y)

binPlusIncOne : One a -> One b -> binPlus (inc a) b = inc (binPlus a b)
binPlusIncOne OneEmpty OneEmpty = Refl
binPlusIncOne OneEmpty (OneO OneEmpty) = Refl
binPlusIncOne OneEmpty (OneO (OneO x)) = Refl
binPlusIncOne OneEmpty (OneO (OneI x)) = Refl
binPlusIncOne OneEmpty (OneI OneEmpty) = Refl
binPlusIncOne OneEmpty (OneI (OneO x)) = Refl
binPlusIncOne OneEmpty (OneI (OneI x)) = Refl
binPlusIncOne (OneO x) OneEmpty = Refl
binPlusIncOne (OneO x) (OneO y) = Refl
binPlusIncOne (OneO x) (OneI y) = Refl
binPlusIncOne (OneI OneEmpty) OneEmpty = Refl
binPlusIncOne (OneI (OneO x)) OneEmpty = Refl
binPlusIncOne (OneI (OneI x)) OneEmpty = Refl
binPlusIncOne (OneI x) (OneO y) = cong O (binPlusIncOne x y)
binPlusIncOne (OneI x) (OneI y) = cong I (binPlusIncOne x y)

binPlusInc : {a : Bin} -> (1 _ : Can a) -> (1 _ : Can b) -> binPlus (inc a) b = inc (binPlus a b)
binPlusInc CanZero CanZero = Refl
binPlusInc CanZero (CanOne OneEmpty) = Refl
binPlusInc CanZero (CanOne (OneO x)) = Refl
binPlusInc CanZero (CanOne (OneI x)) = Refl
binPlusInc (CanOne x) CanZero = case x of
  OneEmpty => Refl
  (OneO _) => Refl
  (OneI x) => cong O (
            emptyBinPlusLeftId (inc _)
    `trans` cong inc (sym $ emptyBinPlusLeftId _))
binPlusInc (CanOne x) (CanOne y) = binPlusIncOne x y
binPlusInc {a = Empty} CanZero CanZero impossible

toPlusHomo : (1 a : Nat) -> (b : Nat) -> to (plus a b) = binPlus (to a) (to b)
toPlusHomo 0 0 = Refl
toPlusHomo 0 (S k) = sym $ zBinPlusRightId (incCanCompat (toCanonical k))
toPlusHomo (S k) j = cong inc (toPlusHomo k j) `trans` sym (binPlusInc (toCanonical k) (toCanonical j))

doubleIsShift : (1 _ : One a) -> binPlus a a = O a
doubleIsShift OneEmpty = Refl
doubleIsShift (OneO x) = cong O (doubleIsShift x)
doubleIsShift (OneI x) = cong O (cong inc (doubleIsShift x))

infixr 4 `trans`

mutual
  canonicalForO : (0 _ : One b) -> to (from (O b)) = O b
  canonicalForO x
    =       cong (to . plus (from b)) (plusZeroRightNeutral (from b))
    `trans` toPlusHomo (from b) (from b)
    `trans` cong (binPlus (to (from b))) (canonicalDef (CanOne x))
    `trans` cong (`binPlus` b) (canonicalDef (CanOne x))
    `trans` doubleIsShift x
  
  export
  canonicalDef : {1 b : Bin} -> (1 _ : Can b) -> to (from b) = b
  canonicalDef {b = (O Empty)} CanZero = Refl
  canonicalDef (CanOne x) = case x of
    OneEmpty => Refl
    OneO x   => canonicalForO x
    OneI x   => cong inc (canonicalForO x)
  canonicalDef {b = Empty } CanZero impossible

