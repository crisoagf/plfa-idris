module Book.Part1.Connectives
import Book.Part1.Isomorphism
import Control.Order
import Syntax.PreorderReasoning.Generic

%default total

record Times (0 a : Type) (0 b : Type) where
  constructor MkTimes
  proj1 : a
  proj2 : b

etaTimes : (1 x : Times a b) -> MkTimes (proj1 x) (proj2 x) = x
etaTimes (MkTimes proj1 proj2) = Refl

timesComm : Iso (Times a b) (Times b a)
timesComm = MkIso (\ (MkTimes proj1 proj2) => MkTimes proj2 proj1) (\ (MkTimes proj2 proj1) => MkTimes proj1 proj2) (\ (MkTimes _ _) => Refl) (\ (MkTimes _ _) => Refl)

timesAssoc : Iso (Times (Times a b) c) (Times a (Times b c))
timesAssoc = MkIso (\ (MkTimes (MkTimes a b) c) => MkTimes a (MkTimes b c)) (\ (MkTimes a (MkTimes b c)) => MkTimes (MkTimes a b) c) (\ (MkTimes (MkTimes _ _) _) => Refl) (\ (MkTimes _ (MkTimes _ _)) => Refl)

iffIsoIff : Iso (Times (a -> b) (b -> a)) (Iff a b)
iffIsoIff = MkIso (\ (MkTimes from to) => MkIff from to) (\ (MkIff from to) => MkTimes from to) (\ (MkTimes _ _) => Refl) (\ (MkIff _ _) => Refl)

data T = TT

tElim : (1 w : T) -> w = TT
tElim TT = Refl

tIdentityL : Iso (Times T a) a
tIdentityL = MkIso (\ (MkTimes TT a) => a) (\x => MkTimes TT x) (\ (MkTimes TT a) => Refl) (\y => Refl)

tIdentityR : Iso (Times a T) a
tIdentityR = isoTrans (CalcWith $ 
  |~ Times a T
  <~ Times T a ...( timesComm )) tIdentityL

data Plus : (0 _ : Type) -> (0 _ : Type) -> Type where
  Inj1 : a -> Plus a b
  Inj2 : b -> Plus a b

casePlus : (a -> c) -> (b -> c) -> Plus a b -> c
casePlus f _ (Inj1 x) = f x
casePlus _ g (Inj2 x) = g x

etaPlus : (1 w : Plus a b) -> casePlus Inj1 Inj2 w = w
etaPlus (Inj1 _) = Refl
etaPlus (Inj2 _) = Refl

plusComm : Iso (Plus a b) (Plus b a)
plusComm = MkIso swapPlus swapPlus swapIsSelfInv swapIsSelfInv
  where
    swapPlus : Plus x y -> Plus y x
    swapPlus (Inj1 x) = Inj2 x
    swapPlus (Inj2 x) = Inj1 x
    
    swapIsSelfInv : (x : Plus y z) -> swapPlus (swapPlus x) = x
    swapIsSelfInv (Inj1 x) = Refl
    swapIsSelfInv (Inj2 x) = Refl

plusAssoc : Iso (Plus (Plus a b) c) (Plus a (Plus b c))
plusAssoc = MkIso assocLeft assocRight lrFromTo rlToFrom
  where
    assocLeft  : Plus (Plus x y) z -> Plus x (Plus y z)
    assocLeft (Inj1 (Inj1 x)) = Inj1 x
    assocLeft (Inj1 (Inj2 x)) = Inj2 (Inj1 x)
    assocLeft (Inj2 x) = Inj2 (Inj2 x)
    assocRight : Plus x (Plus y z) -> Plus (Plus x y) z
    assocRight (Inj1 x) = Inj1 (Inj1 x)
    assocRight (Inj2 (Inj1 x)) = Inj1 (Inj2 x)
    assocRight (Inj2 (Inj2 x)) = Inj2 x
    lrFromTo : (x : Plus (Plus y z) w) -> assocRight (assocLeft x) = x
    lrFromTo (Inj1 (Inj1 x)) = Refl
    lrFromTo (Inj1 (Inj2 x)) = Refl
    lrFromTo (Inj2 x) = Refl
    rlToFrom : (y : Plus x (Plus z w)) -> assocLeft (assocRight y) = y
    rlToFrom (Inj1 x) = Refl
    rlToFrom (Inj2 (Inj1 x)) = Refl
    rlToFrom (Inj2 (Inj2 x)) = Refl

data Bot : Type where

botElim : Bot -> a
botElim x impossible

botIdentityL : Iso (Plus Bot a) a
botIdentityL = MkIso (\ (Inj2 x) => x ) Inj2 (\ (Inj2 _) => Refl) (\_ => Refl)

botIdentityR : Iso (Plus a Bot) a
botIdentityR = isoTrans (CalcWith $
  |~ Plus a Bot
  <~ Plus Bot a ...( plusComm )) botIdentityL

public export
LocalExtensionality : Type -> Type -> Type
LocalExtensionality a b = {f, g : a -> b} -> ((x : a) -> (f x = g x)) -> f = g

arrDistribPlus : LocalExtensionality (Plus a b) c -> Iso (Plus a b -> c) (Times (a -> c) (b -> c))
arrDistribPlus ext = MkIso plusIntrod plusElimin (\ f => ext (ieFromTo f)) eiToFrom
  where
    plusIntrod : (Plus a b -> c) -> Times (a -> c) (b -> c)
    plusIntrod f = MkTimes (\x => f (Inj1 x)) (\x => f (Inj2 x))
    plusElimin : Times (x -> z) (y -> z) -> Plus x y -> z
    plusElimin (MkTimes proj1 _    ) (Inj1 y) = proj1 y
    plusElimin (MkTimes _     proj2) (Inj2 y) = proj2 y
    ieFromTo : (x : (Plus a b -> c)) -> (y : Plus a b)
             -> plusElimin (MkTimes (\z => x (Inj1 z)) (\z => x (Inj2 z))) y = x y
    ieFromTo x (Inj1 y) = Refl
    ieFromTo x (Inj2 y) = Refl
    eiToFrom : (y : Times (a -> c) (b -> c))
             -> plusIntrod (plusElimin y) = y
    eiToFrom (MkTimes proj1 proj2) = the (MkTimes (\x => proj1 x) (\x => proj2 x) = MkTimes proj1 proj2) Refl

timesDistribPlus : Iso (Times (Plus a b) c) (Plus (Times a c) (Times b c))
timesDistribPlus = MkIso tpD ptD tpFromTo ptToFrom
  where
    tpD : Times (Plus a b) c -> Plus (Times a c) (Times b c)
    tpD (MkTimes (Inj1 x) proj2) = Inj1 (MkTimes x proj2)
    tpD (MkTimes (Inj2 x) proj2) = Inj2 (MkTimes x proj2)
    ptD : Plus (Times a c) (Times b c) -> Times (Plus a b) c
    ptD (Inj1 (MkTimes proj1 proj2)) = MkTimes (Inj1 proj1) proj2
    ptD (Inj2 (MkTimes proj1 proj2)) = MkTimes (Inj2 proj1) proj2
    tpFromTo : (x : Times (Plus a b) c) -> ptD (tpD x) = x
    tpFromTo (MkTimes (Inj1 x) proj2) = Refl
    tpFromTo (MkTimes (Inj2 x) proj2) = Refl
    ptToFrom : (y : Plus (Times a c) (Times b c)) -> tpD (ptD y) = y
    ptToFrom (Inj1 (MkTimes proj1 proj2)) = Refl
    ptToFrom (Inj2 (MkTimes proj1 proj2)) = Refl

plusDistribTimes : Embedding (Plus (Times a b) c) (Times (Plus a c) (Plus b c))
plusDistribTimes = MkEmbed ptD tpD ptFromTo
  where
    ptD : Plus (Times a b) c -> Times (Plus a c) (Plus b c)
    ptD (Inj1 (MkTimes proj1 proj2)) = MkTimes (Inj1 proj1) (Inj1 proj2)
    ptD (Inj2 x) = MkTimes (Inj2 x) (Inj2 x)
    tpD : Times (Plus a c) (Plus b c) -> Plus (Times a b) c
    tpD (MkTimes (Inj1 x) (Inj1 y)) = Inj1 (MkTimes x y)
    tpD (MkTimes (Inj1 x) (Inj2 y)) = Inj2 y
    tpD (MkTimes (Inj2 x) proj2) = Inj2 x
    ptFromTo : (x : Plus (Times a b) c) -> tpD (ptD x) = x
    ptFromTo (Inj1 (MkTimes proj1 proj2)) = Refl
    ptFromTo (Inj2 x) = Refl

plusWeakDistribTimes : Times (Plus a b) c -> Plus a (Times b c)
plusWeakDistribTimes (MkTimes (Inj1 x) proj2) = Inj1 x
plusWeakDistribTimes (MkTimes (Inj2 x) proj2) = Inj2 (MkTimes x proj2)

plusTimesTraverse : Plus (Times a b) (Times c d) -> Times (Plus a c) (Plus b d)
plusTimesTraverse (Inj1 (MkTimes proj1 proj2)) = MkTimes (Inj1 proj1) (Inj1 proj2)
plusTimesTraverse (Inj2 (MkTimes proj1 proj2)) = MkTimes (Inj2 proj1) (Inj2 proj2)

notTimesPlusTraverse : ({a, b, c, d : Type} -> Times (Plus a c) (Plus b d) -> Plus (Times a b) (Times c d)) -> Void
notTimesPlusTraverse f =
  case f (the (Times (Plus T Void) (Plus Void T)) (MkTimes (Inj1 TT) (Inj2 TT))) of
         (Inj1 (MkTimes proj1 proj2)) => case proj2 of {}
         (Inj2 (MkTimes proj1 proj2)) => case proj1 of {}

