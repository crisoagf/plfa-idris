module Decidable
import Data.Nat
import Isomorphism

IsTrue : Bool -> Type
IsTrue True = ()
IsTrue False = Void

isTrue : (1 b : Bool) -> IsTrue b -> b = True
isTrue True _ = Refl
isTrue False _ impossible

true : (1 b : Bool) -> b = True -> IsTrue b
true True Refl = ()
true False Refl impossible

lteBoolToLTE : (1 a, b : Nat) -> IsTrue (a <= b) -> LTE a b
lteBoolToLTE 0 0 x = LTEZero
lteBoolToLTE 0 (S b) x = LTEZero
lteBoolToLTE (S k) 0 x impossible
lteBoolToLTE (S k) (S j) x = LTESucc (lteBoolToLTE k j x)

lteToLteBool : (b : Nat) -> LTE a b -> IsTrue (a <= b)
lteToLteBool 0 LTEZero = ()
lteToLteBool (S k) LTEZero = ()
lteToLteBool (S right) (LTESucc x) = lteToLteBool right x

notSLteZ : Not (LTE (S m) Z)
notSLteZ LTEZero impossible
notSLteZ (LTESucc x) impossible

notSLteS : Not (LTE m n) -> Not (LTE (S m) (S n))
notSLteS f (LTESucc x) = f x

decLte : (m, n : Nat) -> Dec (LTE m n)
decLte 0 k = Yes LTEZero
decLte (S k) 0 = No notSLteZ
decLte (S k) (S j) with (decLte k j)
  decLte (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
  decLte (S k) (S j) | (No contra) = No (notSLteS contra)

twoLteFour : decLte 2 4 = Yes (LTESucc (LTESucc LTEZero))
twoLteFour = Refl

notFourLteTwo : decLte 4 2 = No (notSLteS (notSLteS (notSLteZ {m = 1})))
notFourLteTwo = Refl

decLt : (m , n : Nat) -> Dec (LT m n)
decLt m n = decLte (S m) n

decEq : (m, n : Nat) -> Dec (m = n)
decEq 0 0 = Yes Refl
decEq 0 (S k) = No (\ x => case x of {})
decEq (S k) 0 = No (\ x => case x of {})
decEq (S k) (S j) = case decEq k j of
                         (Yes prf) => Yes (cong S prf)
                         (No contra) => No (\ Refl => contra Refl)

erase : Dec a -> Bool
erase (Yes _) = True
erase (No _) = False

lteBoolFromDecLte : Nat -> Nat -> Bool
lteBoolFromDecLte m n = erase (decLte m n)

toWitness : {dec : Dec a} -> IsTrue (erase dec) -> a
toWitness {dec = (Yes prf)} _ = prf
toWitness {dec = (No contra)} _ impossible

fromWitness : {dec : Dec a} -> a -> IsTrue (erase dec)
fromWitness {dec = (Yes prf)} _ = ()
fromWitness {dec = (No contra)} a = contra a

pairDec : Dec a -> Dec b -> Dec (a, b)
pairDec (Yes prf) (Yes x) = Yes (prf, x)
pairDec (Yes prf) (No contra) = No (\x => contra (snd x))
pairDec (No contra) _ = No (\x => contra (fst x))

eitherDec : Dec a -> Dec b -> Dec (Either a b)
eitherDec (Yes prf) y = Yes (Left prf)
eitherDec (No contra) (Yes prf) = Yes (Right prf)
eitherDec (No contra) (No f) = No (either contra f)

notDec : Dec a -> Dec (Not a)
notDec (Yes prf) = No (\f => f prf)
notDec (No contra) = Yes contra

arrDec : Dec a -> Dec b -> Dec (a -> b)
arrDec (Yes prf) (No contra) = No (\f => contra (f prf))
arrDec (No contra) _ = Yes (absurd . contra)
arrDec _ (Yes x) = Yes (\y => x)

andPair : {decA : Dec a} -> {decB : Dec b} -> erase decA && erase decB = erase (pairDec decA decB)
andPair {decA = (Yes prf)} {decB = (Yes x)} = Refl
andPair {decA = (Yes prf)} {decB = (No contra)} = Refl
andPair {decA = (No contra)} {decB = decB} = Refl

orEither : {decA : Dec a} -> {decB : Dec b} -> erase decA || erase decB = erase (eitherDec decA decB)
orEither {decA = (Yes prf)} {decB = decB} = Refl
orEither {decA = (No contra)} {decB = (Yes prf)} = Refl
orEither {decA = (No contra)} {decB = (No f)} = Refl

notNot : {decA : Dec a} -> not (erase decA) = erase (notDec decA)
notNot {decA = (Yes prf)} = Refl
notNot {decA = (No contra)} = Refl

iff : Bool -> Bool -> Bool
iff = (==)

iffDec : Dec a -> Dec b -> Dec (Iff a b)
iffDec (Yes prf) (Yes x) = Yes (MkIff (\y => x) (\y => prf))
iffDec (Yes prf) (No contra) = No (\ (MkIff from _ ) => contra (from prf))
iffDec (No contra) (Yes prf) = No (\ (MkIff _    to) => contra (to   prf))
iffDec (No contra) (No f) = Yes (MkIff (absurd . contra) (absurd . f))

iffIff : {decA : Dec a} -> {decB : Dec b} -> iff (erase decA) (erase decB) = erase (iffDec decA decB)
iffIff {decA = (Yes prf)} {decB = (Yes x)} = Refl
iffIff {decA = (Yes prf)} {decB = (No contra)} = Refl
iffIff {decA = (No contra)} {decB = (Yes prf)} = Refl
iffIff {decA = (No contra)} {decB = (No f)} = Refl

minus : (m, n : Nat) -> (nLteM : LTE n m) -> Nat
minus m 0 nLteM = m
minus (S right) (S k) (LTESucc x) = minus right k x

Given : (q : Dec a) -> Type
Given q = IsTrue (erase q)

minus' : (m, n : Nat) -> {nLteM : Given (decLte n m)} -> Nat
minus' m n {nLteM} = minus m n (toWitness nLteM)

IsFalse : Bool -> Type
IsFalse False = ()
IsFalse True  = Void

GivenNot : (q : Dec a) -> Type
GivenNot q = IsFalse (erase q)

toNotWitness : {dec : Dec a} -> GivenNot dec -> Not a
toNotWitness {dec = (Yes prf)} x y impossible
toNotWitness {dec = (No contra)} x y = contra y

fromNotWitness : {dec : Dec a} -> Not a -> GivenNot dec
fromNotWitness {dec = (Yes prf)} x = absurd $ x prf
fromNotWitness {dec = (No contra)} x = ()



