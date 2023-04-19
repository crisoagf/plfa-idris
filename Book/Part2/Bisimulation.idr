module Book.Part2.Bisimulation

import Book.Part2.MorePrim

%default total

infix 4 ~*~

data (~~) : (ctx |- a) -> (ctx |- a) -> Type where
  VarEq : {x : ctx `Has` a} -> Var x ~~ Var x
  LamEq : m ~~ n -> Lam m ~~ Lam n
  AppEq : m ~~ m' -> n ~~ n' -> App m n ~~ App m' n'
  LetEq : m ~~ m' -> n ~~ n' -> Let m n ~~ App (Lam n') m'

-- Limit simulation scope
data Simulating : (ctx |- a) -> Type where
  SimVar : Simulating (Var x)
  SimLam : Simulating n -> Simulating (Lam n)
  SimApp : Simulating m -> Simulating n -> Simulating (App m n)
  SimLet : Simulating m -> Simulating n -> Simulating (Let m n)

dag : (n : ctx |- a) -> {auto 0 inScope : Simulating n} -> ctx |- a
dag (Var x) = Var x
dag (Lam x) = Lam x
dag (x `App` y) = App x y
dag (Let x y) = App (Lam y) x

congVal : {m' : ctx |- a} -> m ~~ m' -> Value m -> Value m'
congVal (LamEq x) VLam = VLam
congVal (LetEq _ _) VNat impossible

congValInv : {m : ctx |- a} -> m ~~ m' -> Value m' -> Value m
congValInv (LamEq x) VLam = VLam
congValInv VarEq VLam impossible

congRename : (f : {0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a) -> m ~~ m' -> rename f m ~~ rename f m'
congRename f VarEq = VarEq
congRename f (LamEq x) = LamEq (congRename (ext f) x)
congRename f (AppEq x y) = AppEq (congRename f x) (congRename f y)
congRename f (LetEq x y) = LetEq (congRename f x) (congRename (ext f) y)

congExts
  :  {f  : {0 a : LambdaType} -> ctx `Has` a -> ctx' |- a}
  -> {f' : {0 a : LambdaType} -> ctx `Has` a -> ctx' |- a}
  -> ({0 a : LambdaType} -> (x : ctx `Has` a) -> f x ~~ f' x)
  -> (x : ctx :< b `Has` a) -> exts f x ~~ exts f' x
congExts g Z = VarEq
congExts g (S x) = congRename S (g x)

congSubst
  :  {f  : {0 a : LambdaType} -> ctx `Has` a -> ctx' |- a}
  -> {f' : {0 a : LambdaType} -> ctx `Has` a -> ctx' |- a}
  -> ({0 a : LambdaType} -> (x : ctx `Has` a) -> f x ~~ f' x)
  -> m ~~ m' -> subst f m ~~ subst f' m'
congSubst g VarEq = g _
congSubst g (LamEq x) = LamEq (congSubst (congExts g) x)
congSubst f (AppEq x y) = AppEq (congSubst f x) (congSubst f y)
congSubst f (LetEq x y) = LetEq (congSubst f x) (congSubst (congExts f) y)
  
congReplace : {n, n' : ctx :< b |- a} -> {m, m' : ctx |- b} -> n ~~ n' -> m ~~ m' -> replace n m ~~ replace n' m'
congReplace x y = congSubst (\ x => case x of { Z => y ; S z => VarEq }) x

data LockLeg : (m', n : ctx |- a) -> Type where
  MkLockLeg : n ~~ n' -> m' -=> n' -> LockLeg m' n

sim : {m, m', n : ctx |- a} -> m ~~ m' -> m -=> n -> LockLeg m' n
sim VarEq y impossible
sim (LamEq x) y impossible
sim (AppEq x z) (IntroAppLeft y) with (sim x y)
  sim (AppEq x z) (IntroAppLeft y) | (MkLockLeg w v) = MkLockLeg (AppEq w z) (IntroAppLeft v)
sim (AppEq x z) (IntroAppRight y w) with (sim z w)
  sim (AppEq x z) (IntroAppRight y w) | (MkLockLeg v s) = MkLockLeg (AppEq x v) (IntroAppRight (congVal x y) s)
sim (AppEq x z) (BetaLam y) = case x of
  LamEq x' => MkLockLeg (congReplace x' z) (BetaLam (congVal z y))
sim (LetEq x z) (IntroLet y) with (sim x y)
  sim (LetEq x z) (IntroLet y) | (MkLockLeg w v) = MkLockLeg (LetEq w z) (IntroAppRight VLam v)
sim (LetEq x z) (BetaLet y) = MkLockLeg (congReplace z x) (BetaLam (congVal x y))

data LockLegInv : (m', n : ctx |- a) -> Type where
  MkLockLegInv : n' ~~ n -> m' -=> n' -> LockLegInv m' n

simInv : {m, m', n : ctx |- a} -> m' ~~ m -> m -=> n -> LockLegInv m' n
simInv VarEq y impossible
simInv (LamEq x) y impossible
simInv (AppEq x z) (IntroAppLeft y) with (simInv x y)
  simInv (AppEq x z) (IntroAppLeft y) | (MkLockLegInv w v) = MkLockLegInv (AppEq w z) (IntroAppLeft v)
simInv (AppEq x z) (IntroAppRight y w) with (simInv z w)
  simInv (AppEq x z) (IntroAppRight y w) | (MkLockLegInv v s) = MkLockLegInv (AppEq x v) (IntroAppRight (congValInv x y) s)
simInv (AppEq x z) (BetaLam y) = case x of
  (LamEq w) => MkLockLegInv (congReplace w z) (BetaLam (congValInv z y))
simInv (LetEq x z) (IntroAppLeft y) = case y of {}
simInv (LetEq x z) (IntroAppRight y w) with (simInv x w)
  simInv (LetEq x z) (IntroAppRight y w) | (MkLockLegInv v s) = MkLockLegInv (LetEq v z) (IntroLet s)
simInv (LetEq x z) (BetaLam y) = MkLockLegInv (congReplace z x) (BetaLet (congValInv x y))

