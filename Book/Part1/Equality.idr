module Book.Part1.Equality

import Control.Relation
import Data.Nat
import Syntax.PreorderReasoning.Generic

%default total

infix 4 `Eq`

data Eq : {a : Type} -> a -> a -> Type where
  Refl : a `Eq` a

sym : {0 x, y : a} -> x `Eq` y -> y `Eq` x
sym Refl = Refl

trans : {0 x, y, z : a} -> x `Eq` y -> y `Eq` z -> x `Eq` z
trans Refl Refl = Refl

cong : (0 f : a -> b) -> x `Eq` y -> f x `Eq` f y
cong _ Refl = Refl

cong2 : (0 f : a -> a -> b) -> x1 `Eq` y1 -> x2 `Eq` y2 -> f x1 x2 `Eq` f y1 y2
cong2 _ Refl Refl = Refl

congMap : {f, g : a -> b} -> f = g -> f x = g x
congMap = cong (\ h => h x)

subst : (0 p : a -> Type) -> x `Eq` y -> p x -> p y
subst _ Refl w = w

-- Eq Reasoning in Idris is done via infix smartness, check out Syntax.PreorderReasoning
data FastDerivation : dom -> dom -> Type where
  (|~) : (0 x : dom) -> FastDerivation x x
  (<~) : Equality.FastDerivation x y -> Step Eq y z -> FastDerivation x z

NonTrivial : FastDerivation x y -> Type
NonTrivial (|~ x) = Void
NonTrivial (z <~ w) = ()

Calc : (deriv : FastDerivation x y) -> {auto isNonTrivial : NonTrivial deriv} -> x `Eq` y
Calc ((|~ _) <~ (_ ... r)) = r
Calc (d@(_ <~ _) <~ (_ ... r)) = Calc d `trans` r

trans' : {x,y,z : _} -> x `Eq` y -> y `Eq` z -> x `Eq` z
trans' xy yz = Calc $
  |~ x
  <~ y ... xy
  <~ z ... yz

-- Exercise
failing
  mutual
    Transitive a Eq where
      transitive = trans''
    
    trans'' : {x,y,z : _} -> x `Eq` y -> y `Eq` z -> x `Eq` z
    trans'' xy yz = CalcSmart $
      |~ x
      <~ y ... xy
      <~ z ... yz

Symmetric a Eq where
  symmetric = sym

Transitive a Eq where
  transitive = trans

fromBuiltin : a = b -> a `Eq` b
fromBuiltin Refl = Refl

plusComm : (m, n : Nat) -> m + n `Eq` n + m
plusComm m Z = CalcSmart {leq = Eq} $
  |~ m + 0
  <~ m     ...(fromBuiltin $ plusZeroRightNeutral m)
  ~= 0 + m
plusComm m (S k) = CalcSmart $
  |~ m + S k
  <~ S (m + k) ...(sym $ fromBuiltin $ plusSuccRightSucc m k)
  <~ S (k + m) ...(cong S (plusComm m k))
  ~= S k + m

-- Exercise skipped, I already used PreorderReasoning in Relations.

-- Skipped rewriting

LeibEq : {a : Type} -> (x, y : a) -> Type
LeibEq x y = (p : a -> Type) -> p x -> p y

[leibRefl] Reflexive a LeibEq where
  reflexive _ px = px

[leibTrans] Transitive a LeibEq where
  transitive xLEqY yLEqZ p px = yLEqZ p (xLEqY p px)

[leibSym] Symmetric a LeibEq where
  symmetric xLEqY p py = xLEqY (\ x0 => p x0 -> p x) (\z => z) py

eqImpliesLeibEq : a `Eq` b -> a `LeibEq` b
eqImpliesLeibEq xEqY p = subst p xEqY

-- Eq only has one constructor, so we can erase it at runtime
irrelevantEq : (0 prf : a `Eq` b) -> a `Eq` b
irrelevantEq Refl = Refl

leibEqImpliesEq : a `LeibEq` b -> a `Eq` b
leibEqImpliesEq xLEqY = irrelevantEq $ xLEqY (a `Eq`) Refl

-- Universe polymorphism isn't applicable to Idris, everything is universe polymorphic
