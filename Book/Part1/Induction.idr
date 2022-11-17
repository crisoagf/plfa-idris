module Book.Part1.Induction

import Book.Part1.Naturals as Nats
import Data.Nat
import Syntax.PreorderReasoning

%default total

public export
plusAssoc : (1 m : Nat) -> (0 n, p : Nat) -> (m + n) + p = m + (n + p)
plusAssoc Z _ _ = Refl
plusAssoc (S m) n p = cong S (plusAssoc m n p)

public export
zRightId : (1 n : Nat) -> n + 0 = n
zRightId Z = Refl
zRightId (S n) = cong S (zRightId n)

plusSucRight : (1 m : Nat) -> (0 n : Nat) -> m + S n = S (m + n)
plusSucRight 0 n = Refl
plusSucRight (S k) n = cong S (plusSucRight k n)

plusComm : (1 m : Nat) -> (0 n : Nat) -> m + n = n + m
plusComm Z n = sym (zRightId n)
plusComm (S m) n = Calc $
  |~ (S m) + n
  ~= S (m + n)
  ~~ S (n + m) ...(cong S (plusComm m n))
  ~= S n + m
  ~~ n + S m   ...(sym (plusSucRight n m))

swap : (0 m, n, p : Nat) -> m + (n + p) = n + (m + p)
swap m n p = Calc $
  |~ m + (n + p) 
  ~~ (m + n) + p ...(sym (plusAssoc m n p))
  ~~ (n + m) + p ...(cong (+ p) (plusComm m n))
  ~~ n + (m + p) ...(plusAssoc n m p)

infixr 4 `trans`

distrib : (1 m : Nat) -> (0 n, p : Nat) -> (m + n) * p = m * p + n * p
distrib 0 n p = Refl
distrib (S m) n p = Calc $
  |~ (S m + n) * p
  ~= S (m + n) * p
  ~= p + (m + n) * p
  ~~ p + (m * p + n * p) ...(cong (p +) (distrib m n p))
  ~~ (p + m * p) + n * p ...(sym (plusAssoc p (m * p) (n * p)))
  ~= S m * p + n * p

timesAssoc : (1 m : Nat) -> (0 n, p : Nat) -> (m * n) * p = m * (n * p)
timesAssoc 0 n p = Refl
timesAssoc (S m) n p = Calc $
  |~ (S m * n) * p
  ~= (n + m * n) * p
  ~~ n * p + (m * n) * p ...(distrib n (m * n) p)
  ~~ n * p + m * (n * p) ...(cong (n * p +) (timesAssoc m n p))
  ~= S m * (n * p)

zRightCancel : (1 n : Nat) -> n * 0 = 0
zRightCancel 0 = Refl
zRightCancel (S k) = zRightCancel k

timesSucRight : (1 n : Nat) -> (0 k : Nat) -> n * S k = n + (n * k)
timesSucRight 0 k = Refl
timesSucRight (S n) k = Calc $
  |~ S n * S k
  ~= S k + n * S k
  ~~ S k + (n + n * k) ...(cong (S k +) (timesSucRight n k))
  ~= S (k + (n + n * k))
  ~~ S ((k + n) + n * k) ...(cong S (sym $ plusAssoc k n (n * k)))
  ~~ S ((n + k) + n * k) ...(cong (S . (+ n * k)) (plusComm k n))
  ~~ S (n + (k + n * k)) ...(cong S (plusAssoc n k (mult n k)))
  ~= S n + (k + n * k)
  ~= S n + (S n * k)

public export
timesComm : (m, n : Nat) -> m * n = n * m
timesComm 0 n = sym $ zRightCancel n
timesComm (S m) n = Calc $
  |~ S m * n
  ~= n + m * n
  ~~ n + n * m ...(cong (n +) (timesComm m n))
  ~~ n * S m ...(sym (timesSucRight n m))

monusZLeftCancel : (1 m : Nat) -> Nats.monus Z m = Z
monusZLeftCancel 0 = Refl
monusZLeftCancel (S _) = Refl

monusAssoc : (1 m : Nat) -> (n : Nat) -> (0 p : Nat) -> (m `monus` n) `monus` p = m `monus` (n + p)
monusAssoc (S m) 0 p = Refl
monusAssoc (S m) (S n) p = monusAssoc m n p
monusAssoc 0 n p = Calc $
  |~ ((0 `monus` n) `monus` p)
  ~~ (0 `monus` p) ...(cong (`monus` p) (monusZLeftCancel n))
  ~~ 0 ...(monusZLeftCancel p)
  ~~ (0 `monus` (n + p)) ...(sym (monusZLeftCancel (n + p)))

expHomo : (0 m : Nat) -> (1 n : Nat) -> (0 p : Nat) -> power m (n + p) = power m n * power m p
expHomo m 0 p = sym $ zRightId (power m p)
expHomo m (S n) p = Calc $
  |~ power m (S n + p)
  ~= power m (S (n + p))
  ~= m * power m (n + p)
  ~~ m * (power m n * power m p) ...(cong (m *) (expHomo m n p))
  ~~ (m * power m n) * power m p ...(sym (timesAssoc m (power m n) (power m p)))
  ~= power m (S n) * power m p

powHomo : (0 m, n : Nat) -> (1 p : Nat) -> power (m * n) p = power m p * power n p
powHomo m n 0 = Refl
powHomo m n (S p) = Calc $
  |~ power (m * n) (S p)
  ~= (m * n) * power (m * n) p
  ~~ (m * n) * (power m p * power n p) ...(cong ((m * n) *) (powHomo m n p))
  ~~ m * (n * (power m p * power n p)) ...(timesAssoc m n (power m p * power n p))
  ~~ m * (power m p * (n * power n p)) ...(cong (m *) . Calc $
    |~ n * (power m p * power n p)
    ~~ (n * power m p) * power n p ...(sym (timesAssoc n (power m p) (power n p)))
    ~~ (power m p * n) * power n p ...(cong (* power n p) (timesComm n (power m p)))
    ~~ power m p * (n * power n p) ...(timesAssoc (power m p) n (power n p)))
  ~~ (m * power m p) * (n * power n p) ...(sym (timesAssoc m (power m p) (n * (power n p))))
  ~= power m (S p) * power n (S p)

expAssoc : (m, n, p : Nat) -> (power (power m n) p) = power m (n * p)
expAssoc m n 0 = cong (power m) (sym $ zRightCancel n)
expAssoc m n (S p) = Calc $
  |~ power (power m n) (S p)
  ~= power m n * power (power m n) p
  ~~ power m n * power m (n * p) ...(cong ((power m n) *) (expAssoc m n p))
  ~~ power m (n + n * p) ...(sym (expHomo m n (mult n p)))
  ~~ power m (n * S p) ...(cong (power m) (sym $ timesSucRight n p))

fromEmpty0 : from Empty = Z
fromEmpty0 = Refl

public export
fromIncHomo : (1 b : Bin) -> from (inc b) = S (from b)
fromIncHomo Empty = Refl
fromIncHomo (O b) = Refl
fromIncHomo (I b) = Calc $
  |~ from (inc (I b)) 
  ~= from (O (inc b))
  ~= 2 * from (inc b) 
  ~~ 2 * S (from b) ...(cong (2 *) (fromIncHomo b))
  ~= S (from b) + (S (from b) + 0)
  ~= S (from b + (S (from b + 0)))
  ~~ S (S (from b + (from b + 0))) ...(cong S (plusSucRight (from b) (plus (from b) 0)))
  ~= S (S (2 * from b))
  ~= S (from (I b))

notToFromId : ((b : Bin) -> to (from b) = b) -> Void
notToFromId f = case f Empty of {}

public export
fromToId : (1 n : Nat) -> from (to n) = n
fromToId 0 = Refl
fromToId (S n) = Calc $
  |~ from (to (S n))
  ~~ S (from (to n)) ...(fromIncHomo (to n))
  ~~ S n ...(cong S (fromToId n))

