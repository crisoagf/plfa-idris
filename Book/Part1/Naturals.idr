module Book.Part1.Naturals

%default total
%hide plus
%hide mult

plus : Nat -> Nat -> Nat
plus Z n = n
plus (S m) n = S (plus m n)

plusElimZ : (m : Nat) -> plus Z m = m
plusElimZ _ = Refl

plusElimS : (m : Nat) -> (n : Nat) -> plus (S m) n = S (plus m n)
plusElimS _ _ = Refl

plustwothreeeqfive : plus 2 3 = 5
plustwothreeeqfive =
  trans (plusElimS 1 3)
        (cong S (trans (plusElimS 0 3)
                       (cong S (plusElimZ 3))))

mult : Nat -> Nat -> Nat
mult Z n = Z
mult (S m) n = plus n (mult m n)

multElimZ : (m : Nat) -> mult Z m = Z
multElimZ _ = Refl

multElimS : (m : Nat) -> (n : Nat) -> mult (S m) n = plus n (mult m n)
multElimS _ _ = Refl

multtwothreeeqsix : mult 2 3 = 6
multtwothreeeqsix =
  trans (multElimS 1 3)
        (cong (plus 3) (trans (multElimS 0 3)
                              (cong (plus 3) (multElimZ 3))))

exp : Nat -> Nat -> Nat
exp m Z = S Z
exp m (S n) = mult m (exp m n)

expthreefoureqeightyone : exp 3 4 = 81
expthreefoureqeightyone = Refl

public export
monus : (1 m : Nat) -> (1 n : Nat) -> Nat
monus m Z = m
monus Z (S m) = Z
monus (S m) (S n) = monus m n

fivemonusthreeeqtwo : monus 5 3 = 2
fivemonusthreeeqtwo = Refl

threemonusfiveeqzero : monus 3 5 = 0
threemonusfiveeqzero = Refl

public export
data Bin : Type where
  Empty : Bin
  O : Bin -> Bin
  I : Bin -> Bin

public export
inc : Bin -> Bin
inc Empty = I Empty
inc (O b) = I b
inc (I b) = O (inc b)

public export
to : Nat -> Bin
to Z = O Empty
to (S n) = inc (to n)

public export
from : Bin -> Nat
from Empty = Z
from (O b) = 2 * from b
from (I b) = S (2 * from b)
