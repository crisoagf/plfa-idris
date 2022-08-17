module Book.Part2.Lambda
import Decidable.Equality
import Book.Part1.Isomorphism

public export
Id : Type
Id = String

public export
data Term : Type where
  Var : Id -> Term
  Lam : Id -> Term -> Term
  App : Term -> Term -> Term
  Zero : Term
  Suc : Term -> Term
  Case : Term -> Term -> Id -> Term -> Term
  Mu : Id -> Term -> Term

two : Term
two = Suc (Suc Zero)

plus : Term
plus = Mu "+" (Lam "m" (Lam "n" (Case (Var "m") (Var "n") "m" (Suc (App (App (Var "+") (Var "m")) (Var "n"))))))

public export
churchTwo : Term
churchTwo = Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))

churchPlus : Term
churchPlus = Lam "m" (Lam "n" (Lam "s" (Lam "z" (App (App (Var "m") (Var "s")) (App (App (Var "n") (Var "s")) (Var "z"))))))
 
public export
suc : Term
suc = Lam "n" (Suc (Var "n"))

mul : Term
mul = Mu "*" (Lam "m" (Lam "n" (Case (Var "m") Zero "m" (App (App plus (Var "n")) (App (App (Var "*") (Var "m")) (Var "n"))))))

churchMul : Term
churchMul = Lam "m" (Lam "n" (Lam "s" (Lam "z" (App (App (Var "m") (App (Var "n") (Var "s"))) (Var "z")))))

public export
data Value : Term -> Type where
  VLam : Value (Lam x n)
  VZero : Value Zero
  VSuc : Value v -> Value (Suc v)

public export
replace : Term -> Id -> Term -> Term
replace (Var x) y z with (decEq x y)
  replace (Var x) x z | (Yes Refl) = z
  replace (Var x) y z | (No contra) = Var x
replace (Lam x w) y z with (decEq x y)
  replace (Lam x w) x z | (Yes Refl) = Lam x w
  replace (Lam x w) y z | (No contra) = Lam x (replace w y z)
replace (App x w) y z = App (replace x y z) (replace w y z)
replace Zero y z = Zero
replace (Suc x) y z = Suc (replace x y z)
replace (Case x w v s) y z with (decEq v y)
  replace (Case x w v s) v z | (Yes Refl) = Case (replace x v z) (replace w v z) v s
  replace (Case x w v s) y z | (No contra) = Case (replace x y z) (replace w y z) v (replace s y z)
replace (Mu x w) y z with (decEq x y)
  replace (Mu x w) x z | (Yes Refl) = Mu x w
  replace (Mu x w) y z | (No contra) = Mu x (replace w y z)

test1 : replace (Lam "z" (App (Var "s") (App (Var "s") (Var "z")))) "s" Lambda.suc
  = Lam "z" (App Lambda.suc (App Lambda.suc (Var "z")))
test1 = Refl

test2 : replace (App Lambda.suc (App Lambda.suc (Var "z"))) "z" Zero
      = App Lambda.suc (App Lambda.suc Zero)
test2 = Refl
--
test3 : replace (Lam "x" (Var "y")) "y" Zero = Lam "x" Zero
test3 = Refl

test4 : replace (Lam "x" (Var "x")) "x" Zero = Lam "x" (Var "x")
test4 = Refl

test5 : replace (Lam "y" (Var "y")) "x" Zero = Lam "y" (Var "y")
test5 = Refl

quizAnswer : replace (Lam "y" (App (Var "x") (Lam "x" (Var "x")))) "x" Zero = Lam "y" (App Zero (Lam "x" (Var "x")))
quizAnswer = Refl

-- replace': Nah...

public export
data ReduceStep : Term -> Term -> Type where
  IntroAppLeft : ReduceStep left left' -> ReduceStep (App left middle) (App left' middle)
  IntroAppRight : Value middle -> ReduceStep right right' -> ReduceStep (App middle right) (App middle right')
  IntroSuc : ReduceStep middle middle' -> ReduceStep (Suc middle) (Suc middle')
  IntroCase : ReduceStep left left' -> ReduceStep (Case left m x n) (Case left' m x n)
  BetaLam : Value v -> ReduceStep (App (Lam x n) v) (replace n x v)
  BetaZero : ReduceStep (Case Zero m x n) m
  BetaSuc : Value v -> ReduceStep (Case (Suc v) m x n) (replace n x v)
  BetaMu : ReduceStep (Mu x m) (replace m x (Mu x m))

quizAnswer1 : ReduceStep (App (Lam "x" (Var "x")) (Lam "x" (Var "x"))) (Lam "x" (Var "x")) 
quizAnswer1 = BetaLam VLam

quizAnswer2 : ReduceStep (App (App (Lam "x" (Var "x")) (Lam "x" (Var "x"))) (Lam "x" (Var "x")))
  (App (Lam "x" (Var "x")) (Lam "x" (Var "x")))
quizAnswer2 = IntroAppLeft $ BetaLam VLam

quizAnswer3 : ReduceStep
  (App (App Lambda.churchTwo Lambda.suc) Zero)
  (App (Lam "z" (App Lambda.suc (App Lambda.suc (Var "z")))) Zero)
quizAnswer3 = IntroAppLeft $ BetaLam VLam

public export
data Reduce : Term -> Term -> Type where
  Refl : Reduce a a
  Trans : (l : Term) -> {m : Term} -> ReduceStep l m -> Reduce m n -> Reduce l n

public export
data LambdaType : Type where
  Arr : LambdaType -> LambdaType -> LambdaType
  LambdaNat : LambdaType

public export
data Context : Type where
  Empty : Context
  Assigned : Context -> Id -> LambdaType -> Context

contextToList : Context -> List (String, LambdaType)
contextToList Empty = []
contextToList (Assigned x y z) = (y,z) :: contextToList x

listToContext : List (String, LambdaType) -> Context
listToContext [] = Empty
listToContext ((x, y) :: xs) = Assigned (listToContext xs) x y

contextToListToContextId : (x : Context) -> listToContext (contextToList x) = x
contextToListToContextId Empty = Refl
contextToListToContextId (Assigned x y z) = rewrite contextToListToContextId x in Refl

listToContextToListId : (y : List (String, LambdaType)) -> contextToList (listToContext y) = y
listToContextToListId [] = Refl
listToContextToListId ((x, y) :: xs) = rewrite listToContextToListId xs in Refl

contextIso : Iso Context (List (Id, LambdaType))
contextIso = MkIso contextToList listToContext contextToListToContextId listToContextToListId

public export
data Lookup : Context -> Id -> LambdaType -> Type where
  Z : Lookup (Assigned xs x a) x a
  S : Not (x = y) -> Lookup xs x a -> Lookup (Assigned xs y b) x a

GivenNot : Dec a -> Type
GivenNot (Yes _) = Void
GivenNot (No  _) = ()

S' : {x,y : Id} -> {auto xNeqY : GivenNot (decEq x y)} -> Lookup xs x a -> Lookup (Assigned xs y b) x a
S' {xNeqY} z with (decEq x y)
  S' {xNeqY = xNeqY} z | (Yes prf) = absurd xNeqY
  S' {xNeqY = xNeqY} z | (No contra) = S contra z

public export
data TypeOf : Context -> Term -> LambdaType -> Type where
  Axiom : Lookup ctx x a -> TypeOf ctx (Var x) a
  IntroArr : TypeOf (Assigned ctx x a) n b -> TypeOf ctx (Lam x n) (Arr a b)
  ElimArr : TypeOf ctx left (Arr a b) -> TypeOf ctx middle a -> TypeOf ctx (App left middle) b
  IntroNZ : TypeOf ctx Zero LambdaNat
  IntroNSuc : TypeOf ctx m LambdaNat -> TypeOf ctx (Suc m) LambdaNat
  IntroNCase :  TypeOf ctx left LambdaNat -> TypeOf ctx middle a -> TypeOf (Assigned ctx x LambdaNat) right a
             -> TypeOf ctx (Case left middle x right) a
  IntroMu : TypeOf (Assigned ctx x a) middle a -> TypeOf ctx (Mu x middle) a

public export
Church : LambdaType -> LambdaType
Church a = Arr (Arr a a) (Arr a a)

public export
typeOfChurchTwo : TypeOf ctx Lambda.churchTwo (Church a)
typeOfChurchTwo = IntroArr . IntroArr . ElimArr (Axiom $ S' Z) $ ElimArr (Axiom $ S' Z) (Axiom Z)

typeOfTwo : TypeOf ctx Lambda.two LambdaNat
typeOfTwo = IntroNSuc (IntroNSuc IntroNZ)

typeOfPlus : TypeOf ctx Lambda.plus (Arr LambdaNat (Arr LambdaNat LambdaNat))
typeOfPlus = IntroMu . IntroArr . IntroArr . IntroNCase (Axiom $ S' Z) (Axiom Z) $
             IntroNSuc $ ElimArr (ElimArr (Axiom . S' . S' $ S' Z) (Axiom Z)) (Axiom $ S' Z)

typeOfTwoPlusTwo : TypeOf ctx (App (App Lambda.plus Lambda.two) Lambda.two) LambdaNat
typeOfTwoPlusTwo = ElimArr (ElimArr typeOfPlus typeOfTwo) typeOfTwo

typeOfChurchPlus : TypeOf ctx Lambda.churchPlus (Arr (Church a) (Arr (Church a) (Church a)))
typeOfChurchPlus = IntroArr . IntroArr . IntroArr . IntroArr $
  ElimArr
    (ElimArr (Axiom . S' . S' $ S' Z) (Axiom $ S' Z))
    (ElimArr
      (ElimArr (Axiom . S' $ S' Z) (Axiom $ S' Z))
      (Axiom Z)
      )

public export
typeOfSuc : TypeOf ctx Lambda.suc (Arr LambdaNat LambdaNat)
typeOfSuc = IntroArr (IntroNSuc (Axiom Z))

typeOfChurchTwoPlusTwo : TypeOf ctx (App (App (App (App Lambda.churchPlus Lambda.churchTwo) Lambda.churchTwo) Lambda.suc) Zero) LambdaNat
typeOfChurchTwoPlusTwo = ElimArr (ElimArr (ElimArr (ElimArr typeOfChurchPlus typeOfChurchTwo) typeOfChurchTwo) typeOfSuc) IntroNZ

lookupInjective : Lookup ctx x a -> Lookup ctx x b -> a = b
lookupInjective Z Z = Refl
lookupInjective Z (S f y) = absurd (f Refl)
lookupInjective (S f y) Z = absurd (f Refl)
lookupInjective (S f y) (S g z) = lookupInjective y z

nope1 : Not (TypeOf Empty (App Zero (Suc Zero)) a)
nope1 (ElimArr (Axiom x) _) impossible
nope1 (ElimArr (IntroArr x) _) impossible
nope1 (ElimArr (ElimArr x z) _) impossible
nope1 (ElimArr IntroNZ _) impossible
nope1 (ElimArr (IntroNSuc x) _) impossible
nope1 (ElimArr (IntroNCase x z w) _) impossible
nope1 (ElimArr (IntroMu x) _) impossible

nope2 : Not (TypeOf Empty (Lam "x" (App (Var "x") (Var "x"))) a)
nope2 (IntroArr (ElimArr (Axiom Z) (Axiom (S f x)))) = f Refl
nope2 (IntroArr (ElimArr (Axiom Z) (Axiom Z))) impossible
nope2 (IntroArr (ElimArr (Axiom (S f x)) y)) = f Refl

typeOfQuizAnswer1 : TypeOf (Assigned (Assigned Empty "y" (Arr LambdaNat LambdaNat)) "x" LambdaNat) (App (Var "y") (Var "x")) LambdaNat
typeOfQuizAnswer1 = ElimArr (Axiom $ S' Z) (Axiom Z)

typeOfQuizAnswer2 : Not (TypeOf (Assigned (Assigned Empty "y" (Arr LambdaNat LambdaNat)) "x" LambdaNat) (App (Var "x") (Var "y")) a)
typeOfQuizAnswer2 (ElimArr (Axiom (S _ (S _ Z))) (Axiom (S _ _))) impossible
typeOfQuizAnswer2 (ElimArr (Axiom (S _ (S _ (S g1 x)))) (Axiom (S _ _))) impossible

typeOfQuizAnswer3 : Not (TypeOf (Assigned Empty "y" (Arr LambdaNat LambdaNat)) (App (Var "y") (Var "x")) a)
typeOfQuizAnswer3 (ElimArr (Axiom Z) (Axiom (S _ Z))) impossible
typeOfQuizAnswer3 (ElimArr (Axiom Z) (Axiom (S _ (S g x)))) impossible
typeOfQuizAnswer3 (ElimArr (Axiom (S _ _)) (Axiom (S _ Z))) impossible
typeOfQuizAnswer3 (ElimArr (Axiom (S _ _)) (Axiom (S _ (S f1 y)))) impossible

typeOfQuizAnswer4 : Not (TypeOf (Assigned Empty "x" a) (App (Var "x") (Var "x")) b)
typeOfQuizAnswer4 (ElimArr (Axiom Z) (Axiom (S _ Z))) impossible
typeOfQuizAnswer4 (ElimArr (Axiom Z) (Axiom (S _ (S g x)))) impossible
typeOfQuizAnswer4 (ElimArr (Axiom Z) (Axiom Z)) impossible
typeOfQuizAnswer4 (ElimArr (Axiom (S _ Z)) (Axiom Z)) impossible
typeOfQuizAnswer4 (ElimArr (Axiom (S _ (S g x))) (Axiom Z)) impossible
typeOfQuizAnswer4 (ElimArr (Axiom (S _ _)) (Axiom (S _ Z))) impossible
typeOfQuizAnswer4 (ElimArr (Axiom (S _ _)) (Axiom (S _ (S f1 y)))) impossible

typeOfQuizAnswer5 : (a : LambdaType ** (b : LambdaType ** (c : LambdaType **
  TypeOf (Assigned (Assigned Empty "x" a) "y" b) (Lam "z" (App (Var "x") (App (Var "y") (Var "z")))) c)))
typeOfQuizAnswer5 = (Arr LambdaNat LambdaNat ** (Arr LambdaNat LambdaNat ** (Arr LambdaNat LambdaNat **
  IntroArr $ ElimArr (Axiom . S' $ S' Z) (ElimArr (Axiom $ S' Z) (Axiom Z)))))

typeOfMul : TypeOf ctx Lambda.mul (Arr LambdaNat (Arr LambdaNat LambdaNat))
typeOfMul = IntroMu $ IntroArr $ IntroArr $ IntroNCase (Axiom $ S' Z) IntroNZ $ ElimArr (ElimArr typeOfPlus (Axiom $ S' Z)) (ElimArr (ElimArr (Axiom $ S' (S' (S' Z))) (Axiom Z)) (Axiom (S' Z)))

typeOfChurchMul : TypeOf ctx Lambda.churchMul (Arr (Church a) (Arr (Church a) (Church a)))
typeOfChurchMul = IntroArr $ IntroArr $ IntroArr $ IntroArr $ ElimArr (ElimArr (Axiom . S' . S' $ S' Z) (ElimArr (Axiom . S' $ S' Z) (Axiom (S' Z)))) (Axiom Z)

