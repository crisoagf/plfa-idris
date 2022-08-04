module Induction

import Naturals as Nats
import Data.Nat

%default total

plusAssoc : (1 m : Nat) -> (0 n, p : Nat) -> (m + n) + p = m + (n + p)
plusAssoc Z _ _ = Refl
plusAssoc (S m) n p = cong S (plusAssoc m n p)

zRightId : (1 n : Nat) -> n + 0 = n
zRightId Z = Refl
zRightId (S n) = cong S (zRightId n)

plusSucRight : (1 m : Nat) -> (0 n : Nat) -> m + S n = S (m + n)
plusSucRight 0 n = Refl
plusSucRight (S k) n = cong S (plusSucRight k n)

plusComm : (1 m : Nat) -> (0 n : Nat) -> m + n = n + m
plusComm Z n = sym (zRightId n)
plusComm (S m) n = trans (cong S (plusComm m n)) (sym (plusSucRight n m))

swap : (0 m, n, p : Nat) -> m + (n + p) = n + (m + p)
swap m n p = trans (sym (plusAssoc m n p)) (trans (cong (+ p) (plusComm m n)) (plusAssoc n m p))

infixr 4 `trans`

distrib : (1 m : Nat) -> (0 n, p : Nat) -> (m + n) * p = m * p + n * p
distrib 0 n p = Refl
distrib (S k) n p
  =       cong (p +) (distrib k n p)
  `trans` sym (plusAssoc p (mult k p) (mult n p))

timesAssoc : (1 m : Nat) -> (0 n, p : Nat) -> (m * n) * p = m * (n * p)
timesAssoc 0 n p = Refl
timesAssoc (S k) n p
  =       distrib n (mult k n) p
  `trans` cong (n * p +) (timesAssoc k n p)

zRightCancel : (1 n : Nat) -> n * 0 = 0
zRightCancel 0 = Refl
zRightCancel (S k) = zRightCancel k

timesSucRight : (1 n : Nat) -> (0 k : Nat) -> n * S k = n + (n * k)
timesSucRight 0 k = Refl
timesSucRight (S j) k = cong (plus (S k)) (timesSucRight j k)
  `trans` cong S (sym $ plusAssoc k j (mult j k))
  `trans` cong (S . (+ mult j k)) (plusComm k j)
  `trans` cong S (plusAssoc j k (mult j k))

timesComm : (m, n : Nat) -> m * n = n * m
timesComm 0 n = sym $ zRightCancel n
timesComm (S k) n
  =       cong (plus n) (timesComm k n)
  `trans` sym (timesSucRight n k)

monusZLeftCancel : (1 m : Nat) -> Nats.monus Z m = Z
monusZLeftCancel 0 = Refl
monusZLeftCancel (S _) = Refl

monusAssoc : (1 m : Nat) -> (n : Nat) -> (0 p : Nat) -> Nats.monus (Nats.monus m n) p = Nats.monus m (n + p)
monusAssoc 0 n p = cong (`Nats.monus` p) (monusZLeftCancel n) `trans` monusZLeftCancel p `trans` sym (monusZLeftCancel (n + p))
monusAssoc (S k) 0 p = Refl
monusAssoc (S k) (S j) p = monusAssoc k j p

expHomo : (0 m : Nat) -> (1 n : Nat) -> (0 p : Nat) -> power m (n + p) = power m n * power m p
expHomo m 0 p = sym $ zRightId (power m p)
expHomo m (S j) p = cong (mult m) (expHomo m j p) `trans` sym (timesAssoc m (power m j) (power m p))

powHomo : (0 m, n : Nat) -> (1 p : Nat) -> power (m * n) p = power m p * power n p
powHomo m n 0 = Refl
powHomo m n (S k)
  =       cong ((m * n)*) (powHomo m n k)
  `trans` timesAssoc m n (mult (power m k) (power n k))
  `trans`   cong (mult m)
    (       sym (timesAssoc n (power m k) (power n k))
    `trans` cong (* power n k) (timesComm n (power m k))
    `trans` timesAssoc (power m k) n (power n k)
    )
  `trans` sym (timesAssoc m (power m k) (mult n (power n k)))

expAssoc : (m, n, p : Nat) -> (power (power m n) p) = power m (n * p)
expAssoc m n 0 = cong (power m) (sym $ zRightCancel n)
expAssoc m n (S k) = cong ((power m n) *) (expAssoc m n k) `trans` sym (expHomo m n (mult n k)) `trans` cong (power m) (sym $ timesSucRight n k)

fromEmpty0 : from Empty = Z
fromEmpty0 = Refl

public export
fromIncHomo : (1 b : Bin) -> from (inc b) = S (from b)
fromIncHomo Empty = Refl
fromIncHomo (O x) = Refl
fromIncHomo (I x) = cong (2 *) (fromIncHomo x) `trans` cong S (plusSucRight (from x) (plus (from x) 0))

notToFromId : ((b : Bin) -> to (from b) = b) -> Void
notToFromId f = case f Empty of {}

public export
fromToId : (1 n : Nat) -> from (to n) = n
fromToId 0 = Refl
fromToId (S k) = fromIncHomo (to k) `trans` cong S (fromToId k)

