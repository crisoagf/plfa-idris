module Book.Part1.Relations
import Data.Nat
import Book.Part1.Naturals
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

data (<=) : Nat -> Nat -> Type where
  LtEZ : 0 <= m
  LtES : n <= m -> S n <= S m

elimSLtES : S n <= S m -> n <= m
elimSLtES (LtES x) = x

elimMLtZ : m <= 0 -> m = 0
elimMLtZ LtEZ = Refl

ltERefl : {1 n : Nat} -> n <= n
ltERefl {n = 0} = LtEZ
ltERefl {n = (S k)} = LtES ltERefl

Reflexive Nat (<=) where
  reflexive = ltERefl

ltETrans : m <= n -> n <= p -> m <= p
ltETrans LtEZ y = LtEZ
ltETrans (LtES x) (LtES y) = LtES (ltETrans x y)

Transitive Nat (<=) where
  transitive = ltETrans

Preorder Nat (<=) where

ltEAntisym : m <= n -> n <= m -> m = n
ltEAntisym LtEZ LtEZ = Refl
ltEAntisym (LtES x) (LtES y) = cong S (ltEAntisym x y)

data Related : (t : Type) -> (t -> t -> Type) -> t -> t -> Type where
  Direct  : rel a b -> Related t rel a b
  Inverse : rel b a -> Related t rel a b

Total : (t : Type) -> (t -> t -> Type) -> Type
Total t rel = (a, b : t) -> Related t rel a b

ltETotal : Total Nat (<=)
ltETotal 0 0 = Direct LtEZ
ltETotal 0 (S k) = Direct LtEZ
ltETotal (S k) 0 = Inverse LtEZ
ltETotal (S k) (S j) = case ltETotal k j of
                            (Direct x) => Direct (LtES x)
                            (Inverse x) => Inverse (LtES x)

plusLtEMonoRight : (1 p : Nat) -> m <= n -> p + m <= p + n
plusLtEMonoRight 0 x = x
plusLtEMonoRight (S k) x = LtES (plusLtEMonoRight k x)

plusLtEMonoLeft : {m, n : Nat} -> (p : Nat) -> m <= n -> m + p <= n + p
plusLtEMonoLeft {m} {n} p x = CalcWith $
  |~ m + p
  ~~ p + m ...(plusCommutative m p)
  <~ p + n ...(plusLtEMonoRight p x)
  ~~ n + p ...(plusCommutative p n)

plusLtEMono : {m, n, p, q : Nat} -> m <= n -> p <= q -> m + p <= n + q
plusLtEMono {m} {n} {p} {q} x y = CalcWith $
  |~ m + p
  <~ n + p ...(plusLtEMonoLeft  p x)
  <~ n + q ...(plusLtEMonoRight n y)

multLtEMonoRight : (m, n : Nat) -> (1 p : Nat) -> m <= n -> p * m <= p * n
multLtEMonoRight m n 0 x = LtEZ
multLtEMonoRight m n (S p) x = plusLtEMono x (multLtEMonoRight m n p x)

multLtEMonoLeft : (m, n : Nat) -> (p : Nat) -> m <= n -> m * p <= n * p
multLtEMonoLeft m n p x = rewrite multCommutative m p in
                          rewrite multCommutative n p in multLtEMonoRight m n p x

multLtEMono : {m, n, p, q : Nat} -> m <= n -> p <= q -> m * p <= n * q
multLtEMono {m} {n} {p} {q} x y = multLtEMonoLeft m n p x `ltETrans` multLtEMonoRight p q n y

data (<) : Nat -> Nat -> Type where
  LtZ : Z < S m
  LtS : m < n -> S m < S n

ltTrans : m < n -> n < p -> m < p
ltTrans LtZ (LtS x) = LtZ
ltTrans (LtS x) (LtS y) = LtS (ltTrans x y)

Transitive Nat (<) where
  transitive = ltTrans

data TrichotomyAt : (t : Type) -> (rel : t -> t -> Type) -> t -> t -> Type where
  TriRefl : TrichotomyAt t rel a a
  TriDirect  : rel a b -> TrichotomyAt t rel a b
  TriInverse : rel b a -> TrichotomyAt t rel a b

Trichotomy : (t : Type) -> (t -> t -> Type) -> Type
Trichotomy t rel = (a, b : t) -> TrichotomyAt t rel a b

ltTrichotomy : Trichotomy Nat (<)
ltTrichotomy 0 0 = TriRefl
ltTrichotomy 0 (S k) = TriDirect LtZ
ltTrichotomy (S k) 0 = TriInverse LtZ
ltTrichotomy (S k) (S j) = case ltTrichotomy k j of
                                  TriRefl => TriRefl
                                  (TriDirect x) => TriDirect (LtS x)
                                  (TriInverse x) => TriInverse (LtS x)

plusLtMonoRight : (1 p : Nat) -> m < n -> p + m < p + n
plusLtMonoRight 0 x = x
plusLtMonoRight (S k) x = LtS (plusLtMonoRight k x)

-- The tail needs to be <~ for CalcSmart to work
plusLtMonoLeft : {m, n : Nat} -> (p : Nat) -> m < n -> m + p < n + p
plusLtMonoLeft {m} {n} p x = CalcSmart {leq = (<)} $
  |~ m + p
  ~~ p + m ...(plusCommutative m p)
  <~ p + n ...(plusLtMonoRight p x)
  ~~ n + p ...(plusCommutative p n)

plusLtMono : {m, n, p, q : Nat} -> m < n -> p < q -> m + p < n + q
plusLtMono x y = CalcSmart $
  |~ m + p
  <~ n + p ...(plusLtMonoLeft p x)
  <~ n + q ...(plusLtMonoRight n y)

ltEToLt : S m <= n -> m < n
ltEToLt (LtES LtEZ) = LtZ
ltEToLt (LtES (LtES x)) = LtS (ltEToLt (LtES x))

ltToLtE : m < n -> S m <= n
ltToLtE LtZ = LtES LtEZ
ltToLtE (LtS x) = LtES (ltToLtE x)

dropAnS : S m <= n -> m <= n
dropAnS (LtES LtEZ) = LtEZ
dropAnS (LtES (LtES x)) = LtES (dropAnS (LtES x))

ltTrans' : m < n -> n < p -> m < p
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
data Canonical : Bin -> Type where
  CanonicalZero : Canonical (O Empty)
  CanonicalOne : One b -> Canonical b

incOneCompat : One b -> One (inc b)
incOneCompat OneEmpty = OneO OneEmpty
incOneCompat (OneO x) = OneI x
incOneCompat (OneI x) = OneO (incOneCompat x)

incCanonicalCompat : Canonical b -> Canonical (inc b)
incCanonicalCompat CanonicalZero = CanonicalOne OneEmpty
incCanonicalCompat (CanonicalOne x) = CanonicalOne (incOneCompat x)

export
toCanonical : (1 n : Nat) -> Canonical (to n)
toCanonical 0 = CanonicalZero
toCanonical (S k) = incCanonicalCompat (toCanonical k)

(+) : (b, c : Bin) -> Bin
(+) Empty c = c
(+) b Empty = b
(+) (O x) (O y) = O (x + y)
(+) (O x) (I y) = I (x + y)
(+) (I x) (O y) = I (x + y)
(+) (I x) (I y) = O (inc (x + y))

emptyPlusLeftId : (1 b : Bin) -> b + Empty = b
emptyPlusLeftId Empty = Refl
emptyPlusLeftId (O x) = Refl
emptyPlusLeftId (I x) = Refl

zeroPlusLeftId : {b : Bin} -> (_ : Canonical b) -> b + O Empty = b
zeroPlusLeftId CanonicalZero = Refl
zeroPlusLeftId (CanonicalOne x) = case x of
  OneEmpty => Refl
  (OneO x) => cong O (emptyPlusLeftId _)
  (OneI x) => cong I (emptyPlusLeftId _)

zeroPlusRightId : (_ : Canonical b) -> O Empty + b = b
zeroPlusRightId CanonicalZero = Refl
zeroPlusRightId (CanonicalOne OneEmpty) = Refl
zeroPlusRightId (CanonicalOne (OneO x)) = Refl
zeroPlusRightId (CanonicalOne (OneI x)) = Refl

plusOneCompat : {b : Bin} -> One b -> One c -> One (b + c)
plusOneCompat OneEmpty OneEmpty = OneO OneEmpty
plusOneCompat OneEmpty (OneO x) = OneI x
plusOneCompat OneEmpty (OneI x) = OneO (incOneCompat x)
plusOneCompat {b = O b} (OneO x) OneEmpty = rewrite emptyPlusLeftId b in OneI x
plusOneCompat {b = I b} (OneI x) OneEmpty = rewrite emptyPlusLeftId b in OneO (incOneCompat x)
plusOneCompat (OneO x) (OneO y) = OneO (plusOneCompat x y)
plusOneCompat (OneO x) (OneI y) = OneI (plusOneCompat x y)
plusOneCompat (OneI x) (OneO y) = OneI (plusOneCompat x y)
plusOneCompat (OneI x) (OneI y) = OneO (incOneCompat (plusOneCompat x y))

plusCanonicalCompat : {b : Bin} -> Canonical b -> Canonical c -> Canonical (b + c)
plusCanonicalCompat CanonicalZero    CanonicalZero = CanonicalZero
plusCanonicalCompat CanonicalZero    (CanonicalOne OneEmpty) = CanonicalOne OneEmpty
plusCanonicalCompat CanonicalZero    (CanonicalOne (OneO x)) = CanonicalOne (OneO x)
plusCanonicalCompat CanonicalZero    (CanonicalOne (OneI x)) = CanonicalOne (OneI x)
plusCanonicalCompat x                CanonicalZero = rewrite zeroPlusLeftId x in x
plusCanonicalCompat (CanonicalOne x) (CanonicalOne y) = CanonicalOne (plusOneCompat x y)

plusIncOne : One a -> One b -> inc a + b = inc (a + b)
plusIncOne OneEmpty OneEmpty = Refl
plusIncOne OneEmpty (OneO OneEmpty) = Refl
plusIncOne OneEmpty (OneO (OneO x)) = Refl
plusIncOne OneEmpty (OneO (OneI x)) = Refl
plusIncOne OneEmpty (OneI OneEmpty) = Refl
plusIncOne OneEmpty (OneI (OneO x)) = Refl
plusIncOne OneEmpty (OneI (OneI x)) = Refl
plusIncOne (OneO x) OneEmpty = Refl
plusIncOne (OneO x) (OneO y) = Refl
plusIncOne (OneO x) (OneI y) = Refl
plusIncOne (OneI OneEmpty) OneEmpty = Refl
plusIncOne (OneI (OneO x)) OneEmpty = Refl
plusIncOne (OneI (OneI x)) OneEmpty = Refl
plusIncOne (OneI x) (OneO y) = cong O (plusIncOne x y)
plusIncOne (OneI x) (OneI y) = cong I (plusIncOne x y)

plusInc : {a : Bin} -> (1 _ : Canonical a) -> (1 _ : Canonical b) -> inc a + b = inc (a + b)
plusInc CanonicalZero CanonicalZero = Refl
plusInc CanonicalZero (CanonicalOne OneEmpty) = Refl
plusInc CanonicalZero (CanonicalOne (OneO x)) = Refl
plusInc CanonicalZero (CanonicalOne (OneI x)) = Refl
plusInc {a = Empty} (CanonicalOne z) CanonicalZero impossible
plusInc {a = (O y)} (CanonicalOne Empty) CanonicalZero impossible
plusInc {a = (O y)} (CanonicalOne (OneO x)) CanonicalZero = Refl
plusInc {a = (O y)} (CanonicalOne (OneI x)) CanonicalZero impossible
plusInc {a = (I Empty)} (CanonicalOne OneEmpty) CanonicalZero = Refl
plusInc {a = (I y)} (CanonicalOne (OneI x)) CanonicalZero = cong O . Calc $
  |~ inc y + Empty 
  ~~ inc y ...(emptyPlusLeftId (inc y))
  ~~ inc (y + Empty) ...(cong inc (sym $ emptyPlusLeftId y))
plusInc (CanonicalOne x) (CanonicalOne y) = plusIncOne x y
plusInc {a = Empty} CanonicalZero CanonicalZero impossible

toPlusHomo : (1 a : Nat) -> (b : Nat) -> to (a + b) = to a + to b
toPlusHomo 0 0 = Refl
toPlusHomo 0 (S b) = sym $ zeroPlusRightId (incCanonicalCompat (toCanonical b))
toPlusHomo (S a) b = Calc $
  |~ to (S a + b)
  ~= to (S (a + b))
  ~= inc (to (a + b))
  ~~ inc (to a + to b) ...(cong inc (toPlusHomo a b))
  ~~ (inc (to a) + to b) ...(sym (plusInc (toCanonical a) (toCanonical b)))
  ~= to (S a) + to b

doubleIsShift : (1 _ : One a) -> a + a = O a
doubleIsShift OneEmpty = Refl
doubleIsShift (OneO x) = cong O (doubleIsShift x)
doubleIsShift (OneI x) = cong O (cong inc (doubleIsShift x))

mutual
  canonicalForO : {b : _} -> (_ : One b) -> to (from (O b)) = O b
  canonicalForO x = Calc $
    |~ to (from (O b))
    ~= to (2 * from b)
    ~= to (from b + (from b + 0))
    ~~ to (from b + from b) ...(cong (to . (from b +)) (plusZeroRightNeutral (from b)))
    ~~ to (from b) + (to (from b)) ...(toPlusHomo (from b) (from b))
    ~~ to (from b) + b ...(cong (to (from b) +) (canonicalDef (CanonicalOne x)))
    ~~ b + b ...(cong (+ b) (canonicalDef (CanonicalOne x)))
    ~~ O b ...(doubleIsShift x)
  
  export
  canonicalDef : {1 b : Bin} -> (1 _ : Canonical b) -> to (from b) = b
  canonicalDef {b = (O Empty)} CanonicalZero = Refl
  canonicalDef (CanonicalOne x) = case x of
    OneEmpty => Refl
    OneO x   => canonicalForO x
    OneI x   => cong inc (canonicalForO x)
  canonicalDef {b = Empty } CanonicalZero impossible

