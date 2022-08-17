module Book.Part2.Confluence

import Book.Part1.Quantifiers
import Book.Part2.Untyped
import Book.Appendix.Substitution

diamondCounterexample : ctx |- Star -> ctx |- Star
diamondCounterexample m = Lam (Var Z `App` Var Z) `App` (Lam (Var Z) `App` m)

diamondCounterexample1 : {m : _} -> diamondCounterexample m -=> Lam (Var Z `App` Var Z) `App` m
diamondCounterexample1 = IntroAppRight BetaLam

diamondCounterexample2 : diamondCounterexample m -=> (Lam (Var Z) `App` m) `App` (Lam (Var Z) `App` m)
diamondCounterexample2 = BetaLam

infix 2 ==>
infix 2 ==>>
infixr 2 `Trans`

data (==>) : ctx |- a -> ctx |- a -> Type where
  Pvar : {x : ctx `Has` a} -> Var x ==> Var x
  Pabs : n ==> n' -> Lam n ==> Lam n'
  Papp : {m, m' : _} -> {n, n' : _} -> m ==> m' -> n ==> n' -> m `App` n ==> m' `App` n'
  Pbeta : {m, m' : _} -> {n, n' : _} -> n ==> n' -> m ==> m' -> Lam n `App` m ==> replace n' m'

prefl : {m : _} -> m ==> m
prefl {m = (Var x)} = Pvar
prefl {m = (Lam x)} = Pabs prefl
prefl {m = (x `App` y)} = Papp prefl prefl

data (==>>) : ctx |- a -> ctx |- a -> Type where
  Refl : m ==>> m
  Trans : {m : _} -> l ==> m -> m ==>> n -> l ==>> n

betaPar : {m : _} -> m -=> n -> m ==> n
betaPar (IntroAppLeft x) = Papp (betaPar x) prefl
betaPar (IntroAppRight x) = Papp prefl (betaPar x)
betaPar BetaLam = Pbeta prefl prefl
betaPar (IntroLam x) = Pabs (betaPar x)

betaPars : {m,n : _} -> m -=>> n -> m ==>> n
betaPars Refl = Refl
betaPars (x `Trans` y) = betaPar x `Trans` betaPars y

parBeta : {m,n : _} -> m ==> n -> m -=>> n
parBeta Pvar = Refl
parBeta (Pabs x) = lamCong $ parBeta x
parBeta (Papp x y) = appLCong (parBeta x) >> appRCong (parBeta y)
parBeta (Pbeta x y) = appLCong (lamCong (parBeta x)) >> appRCong (parBeta y) >> (BetaLam `Trans` Refl)

parBetas : {m,n : _} -> m ==>> n -> m -=>> n
parBetas Refl = Refl
parBetas (x `Trans` y) = parBeta x >> parBetas y

ParSubst : Subst ctx ctx' -> Subst ctx ctx' -> Type
ParSubst sigma sigma' = {0 a : LambdaType} -> {x : ctx `Has` a} -> sigma x ==> sigma' x

parRename : FunExt => {rho : Rename ctx ctx'} -> {m, m' : ctx |- _} -> m ==> m' -> rename rho m ==> rename rho m'
parRename Pvar = Pvar
parRename (Pabs x) = Pabs (parRename x)
parRename (Papp x y) = Papp (parRename x) (parRename y)
parRename (Pbeta {m} {n} {m'} {n'} x y) with (Pbeta (parRename {rho = ext rho} x) (parRename {rho} y))
  parRename (Pbeta x y) | g with (renameSubstCommute {m = m'} {n = n'} {rho})
    parRename (Pbeta x y) | g | rsc = replace {p = \ x => Lam (rename (ext rho) n) `App` rename rho m ==> x} rsc g

parSubstExts : FunExt => {sigma, tau : Subst _ _} -> ParSubst sigma tau -> {b : _} -> ParSubst (exts sigma {b}) (exts tau)
parSubstExts f {x = Z} = Pvar
parSubstExts f {x = (S x)} = parRename f

substPar : FunExt => {sigma, tau : Subst _ _} -> ParSubst sigma tau -> m ==> m' -> subst sigma m ==> subst tau m'
substPar f Pvar = f
substPar f (Pabs x) = Pabs (substPar {sigma = exts sigma} {tau = exts tau} (parSubstExts {sigma} {tau} f) x)
substPar f (Papp x y) = Papp (substPar {sigma} {tau} f x) (substPar {sigma} {tau} f y)
substPar f (Pbeta {m} {n} {m'} {n'} x y) with (Pbeta (substPar {sigma = exts sigma} {tau = exts tau} (parSubstExts {sigma} {tau} f) x) (substPar {sigma} {tau} f y))
  substPar f (Pbeta x y) | g = replace {p = \ x => Lam (subst (exts sigma) n) `App` subst sigma m ==> x} substCommute g

parSubstZero : m ==> m' -> ParSubst (substZero m) (substZero m')
parSubstZero y {x = Z} = y
parSubstZero y {x = (S x)} = Pvar

subPar : FunExt => {n,n' : _ |- _} -> {m,m' : _} -> n ==> n' -> m ==> m' -> replace n m ==> replace n' m'
subPar nn' mm' = substPar {sigma = substZero m} {tau = substZero m'} (parSubstZero mm') nn'

fullEval : ctx |- a -> ctx |- a
fullEval (Var x) = Var x
fullEval (Lam x) = Lam (fullEval x)
fullEval ((Lam x) `App` y) = replace (fullEval x) (fullEval y)
fullEval (x `App` y) = fullEval x `App` fullEval y

parTriangle : FunExt => m ==> n -> n ==> fullEval m
parTriangle Pvar = Pvar
parTriangle (Pabs x) = Pabs (parTriangle x)
parTriangle (Papp {m = (Var z)} x y) = Papp (parTriangle x) (parTriangle y)
parTriangle (Papp {m = (z `App` w)} x y) = Papp (parTriangle x) (parTriangle y)
parTriangle (Papp {m = (Lam z)} x y) with (parTriangle x)
  parTriangle (Papp {m = (Lam z)} x y) | (Pabs w) = Pbeta w (parTriangle y)
parTriangle (Pbeta {m} {n} {m'} {n'} x y) with (parTriangle x)
  parTriangle (Pbeta {m} {n} {m'} {n'} x y) | trix with (parTriangle y)
    parTriangle (Pbeta {m} {n} {m'} {n'} x y) | trix | triy = subPar trix triy

parDiamond : FunExt => {m : _} -> m ==> n -> m ==> n' -> (l : _ ** (n ==> l, n' ==> l))
parDiamond {m} x y = (fullEval m ** (parTriangle x, parTriangle y))


parDiamondDirect : FunExt => {m : _} -> m ==> n -> m ==> n' -> (l : _ ** (n ==> l, n' ==> l))
parDiamondDirect Pvar Pvar = MkDPair (Var _) (Pvar, Pvar)
parDiamondDirect (Pabs x) (Pabs y) with (parDiamondDirect x y)
  parDiamondDirect (Pabs x) (Pabs y) | (MkDPair fst (z, w)) = MkDPair (Lam fst) (Pabs z, Pabs w)
parDiamondDirect (Papp x z) (Papp y w) with (parDiamondDirect x y)
  parDiamondDirect (Papp x z) (Papp y w) | (MkDPair fst snd) with (parDiamondDirect z w)
    parDiamondDirect (Papp x z) (Papp y w) | (MkDPair fst (t, u)) | (MkDPair v (s, y1)) = MkDPair (fst `App` v) (Papp t s, Papp u y1)
parDiamondDirect (Pbeta x z) (Pbeta y w) with (parDiamondDirect x y)
  parDiamondDirect (Pbeta x z) (Pbeta y w) | (MkDPair fst (v, s)) with (parDiamondDirect z w)
    parDiamondDirect (Pbeta x z) (Pbeta y w) | (MkDPair fst (v, s)) | (MkDPair t (u, y1)) = MkDPair (replace fst t) (subPar v u, subPar s y1)
parDiamondDirect (Papp x z) (Pbeta y w) = case x of
  (Pabs v) => case parDiamondDirect v y of
                   (MkDPair fst (s, t)) => case parDiamondDirect z w of
                                                (MkDPair u (x1, y1)) => MkDPair (replace fst u) (Pbeta s x1, subPar t y1)
parDiamondDirect (Pbeta x z) (Papp y w) with (parDiamondDirect z w)
  parDiamondDirect (Pbeta x z) (Papp y w) | (MkDPair fst (v, s)) = case y of
    (Pabs t) => case parDiamondDirect x t of
                     (MkDPair u (x1, y1)) => MkDPair (replace u fst) (subPar x1 v, Pbeta y1 s)


strip : FunExt => {m, n : _} -> m ==> n -> m ==>> n' -> (l : _ ** (n ==>> l, n' ==> l))
strip x Refl = (_ ** (Refl, x))
strip x (y `Trans` z) with (parDiamond x y)
  strip x (y `Trans` z) | (MkDPair fst (w, v)) with (strip v z)
    strip x (y `Trans` z) | (MkDPair fst (w, v)) | (MkDPair s (t, u)) = (_ ** (w `Trans` t, u))

parConfluence : FunExt => {m, n, n' : _} -> m ==>> n -> m ==>> n' -> (l : _ ** (n ==>> l, n' ==>> l))
parConfluence Refl y = (_ ** (y, Refl))
parConfluence (x `Trans` z) y with (strip x y)
  parConfluence (x `Trans` z) y | (MkDPair fst (w, v)) with (parConfluence z w)
    parConfluence (x `Trans` z) y | (MkDPair fst (w, v)) | (MkDPair s (t, u)) = (s ** (t, v `Trans` u))

confluence : FunExt => {m, n, n' : _} -> m -=>> n -> m -=>> n' -> (l : _ ** (n -=>> l, n' -=>> l))
confluence x y with (parConfluence (betaPars x) (betaPars y))
  confluence x y | (MkDPair fst (z, w)) = MkDPair fst (parBetas z, parBetas w)

