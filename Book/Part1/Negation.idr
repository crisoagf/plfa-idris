module Book.Part1.Negation
import Book.Part1.Connectives
import Book.Part1.Isomorphism
import Data.Nat

%default total

notNotIntro : a -> Not (Not a)
notNotIntro a nota = case nota a of {}

notNotNotElim : Not (Not (Not a)) -> Not a
notNotNotElim notnotnota a = notnotnota (notNotIntro a)

contraposition : (a -> b) -> Not b -> Not a
contraposition f notb = notb . f

Neq : a -> a -> Type
Neq a b = Not (a = b)

neq12 : Neq 1 2
neq12 Refl impossible

peano : Neq Z (S n)
peano Refl impossible

assimilation : LocalExtensionality a Void -> (negx, negx' : Not a) -> negx = negx'
assimilation ext negx negx' = ext (\ x => case negx x of {})

ltIrreflexive : Not (LT a a)
ltIrreflexive (LTESucc x) = ltIrreflexive x

data TrichotomyAt : {0 a : Type} -> (0 rel : a -> a -> Type) -> (0 _ : a) -> (0 _ : a) -> Type where
  Refl    : {x : a} -> Not (rel x x) -> TrichotomyAt rel x x
  Direct  : {x,y : a} -> rel x y -> Not (rel y x) -> TrichotomyAt rel x y
  Inverse : {x,y : a} -> rel y x -> Not (rel x y) -> TrichotomyAt rel x y

Trichotomy : {a : Type} -> (rel : a -> a -> Type) -> Type
Trichotomy rel = (x,y : a) -> TrichotomyAt rel x y

ltTrich : Trichotomy LT
ltTrich 0 0 = Refl ltIrreflexive
ltTrich 0 (S k) = Direct (LTESucc LTEZero) (\ x => case x of {})
ltTrich (S k) 0 = Inverse (LTESucc LTEZero) (\ x => case x of {})
ltTrich (S k) (S j) = case ltTrich k j of
                           (Refl      f) => Refl                (\ (LTESucc x) => f x)
                           (Direct  x f) => Direct  (LTESucc x) (\ (LTESucc x) => f x)
                           (Inverse x f) => Inverse (LTESucc x) (\ (LTESucc x) => f x)

notPlusToTimesNot : Not (Either a b) -> Pair (Not a) (Not b)
notPlusToTimesNot f = (\x => f (Left x), \x => f (Right x))

timesNotToNotPlus : Pair (Not a) (Not b) -> Not (Either a b)
timesNotToNotPlus x (Left y) = fst x y
timesNotToNotPlus x (Right y) = snd x y

notPlusIsoTimesNot : LocalExtensionality (Either a b) Void -> Iso (Not (Either a b)) (Pair (Not a) (Not b))
notPlusIsoTimesNot ext = MkIso notPlusToTimesNot timesNotToNotPlus leftInv rightInv
  where
    leftInv : (x : (Either a b -> Void)) -> timesNotToNotPlus (\z => x (Left z), \z => x (Right z)) = x
    leftInv x = assimilation ext (timesNotToNotPlus (\z => x (Left z), \z => x (Right z))) x
    rightInv : (y : (a -> Void, b -> Void)) -> (\x => fst y x, \x => snd y x) = y
    rightInv (x, y) = Refl

plusNotToNotTimes : Either (Not a) (Not b) -> Not (Pair a b)
plusNotToNotTimes (Left x) (y, z) = x y
plusNotToNotTimes (Right x) (y, z) = x z

-- Not provable in intuitionistic logic!
-- notTimesToPlusNot : Not (Pair a b) -> Either (Not a) (Not b)
-- notTimesToPlusNot f = ?notTimesToPlusNot_rhs

ExcludedMiddle : Type
ExcludedMiddle = (a : Type) -> Either a (Not a)

emIrrefutable : Not (Not (Either a (Not a)))
emIrrefutable f = f (Right (\ a => f (Left a)))

DoubleNegationElimination : Type
DoubleNegationElimination = (a : Type) -> Not (Not a) -> a

emImpliesDne : ExcludedMiddle -> DoubleNegationElimination 
emImpliesDne f a g = case f a of
                        (Left x) => x
                        (Right x) => case g x of {}

PeircesLaw : Type
PeircesLaw = (a, b : Type) -> ((a -> b) -> a) -> a

dneImpliesPeirce : DoubleNegationElimination -> PeircesLaw
dneImpliesPeirce f a b g = f a $ \ nota => contraposition g nota $ \ anA => case nota anA of {}

peirceImpliesEm : PeircesLaw -> ExcludedMiddle
peirceImpliesEm f a = either Right Left $
  f (Either (a -> Void) a) (Not a) $ \ emElim => Left $ \ a => emElim (Right a) a

ImplicationAsDisjunction : Type
ImplicationAsDisjunction = (a, b : Type) -> (a -> b) -> Either (Not a) b

peirceimpliesArrToEither : PeircesLaw -> ImplicationAsDisjunction 
peirceimpliesArrToEither f a b g = either (Right . g) Left $ peirceImpliesEm f a

arrToEitherImpliesEm : ImplicationAsDisjunction -> ExcludedMiddle
arrToEitherImpliesEm f a = either Right Left $ f a a id

arrToEitherImpliesDne : ImplicationAsDisjunction -> DoubleNegationElimination
arrToEitherImpliesDne f = emImpliesDne (arrToEitherImpliesEm f)

DeMorgan : Type
DeMorgan = (a, b : Type) -> Not (Not a, Not b) -> Either a b

arrToEitherImpliesDeMorgan : ImplicationAsDisjunction -> DeMorgan
arrToEitherImpliesDeMorgan f a b g = either (Left . arrToEitherImpliesDne f a) Right $
  f (a -> Void) b (\ nota => arrToEitherImpliesDne f b $ \ notb => g (nota, notb))

deMorganImpliesEm : DeMorgan -> ExcludedMiddle
deMorganImpliesEm f a = f a (Not a) (\ (nota, notnota) => notnota nota)

Stable : Type -> Type
Stable a = Not (Not a) -> a

notIsStable : Stable (Not a)
notIsStable = notNotNotElim

stableConj : Stable a -> Stable b -> Stable (a, b)
stableConj f g f1 = (f $ \ nota => f1 (nota . fst), g $ \ notb => f1 (notb . snd))

