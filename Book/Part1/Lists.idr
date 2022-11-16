module Book.Part1.Lists
import Book.Part1.Naturals
import Book.Part1.Induction
import Book.Part1.Isomorphism
import Control.Function.FunExt
import Data.List
import Data.List.Quantifiers as Qs
import Data.Nat
import Syntax.PreorderReasoning
import Syntax.EqReasoning

%default total

append : (1 l1 : List a) -> (l2 : List a) -> List a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

appendAssoc : (xs, ys, zs : List a) -> append (append xs ys) zs = append xs (append ys zs)
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = Calc $ 
  |~ append (append (x :: xs) ys) zs
  ~~ append (x :: append xs ys) zs ...(Refl)
  ~~ x :: append (append xs ys) zs ...(Refl)
  ~~ x :: append xs (append ys zs) ...(cong (x ::) (appendAssoc xs ys zs))
  ~~ append (x :: xs) (append ys zs) ...(Refl)

appendRightId : (xs : List a) -> append xs [] = xs
appendRightId [] = Refl
appendRightId (x :: xs) = cong (x ::) (appendRightId xs)

lengthHomo : (xs, ys : List a) -> length (append xs ys) = length xs + length ys
lengthHomo [] ys = Refl
lengthHomo (x :: xs) ys = cong S (lengthHomo xs ys)

revOnto' : (xs, ys : List a) -> reverseOnto xs ys = append (reverse ys) xs
revOnto' xs [] = Refl
revOnto' xs (x :: ys) =
  rewrite revOnto' (x :: xs) ys in
  rewrite sym $ appendAssoc (reverse ys) [x] xs in
  rewrite sym $ revOnto' [x] ys in Refl

reverseDistrib : (xs, ys : List a) -> reverse (append xs ys) = append (reverse ys) (reverse xs)
reverseDistrib [] xs = sym $ appendRightId (reverse xs)
reverseDistrib (x :: xs) ys = rewrite revOnto' [x] (append xs ys) in
                              rewrite reverseDistrib xs ys in
                              rewrite appendAssoc (reverse ys) (reverse xs) [x] in
                              rewrite sym (revOnto' [x] xs) in Refl

-- reverseInvolutive : (xs : List a) -> reverse (reverse xs) = xs
-- reverseInvolutive [] = Refl
-- reverseInvolutive (x :: xs) =
--   rewrite revOnto' [x] xs in
--   rewrite reverseDistrib (reverse xs) [x] in
--   rewrite the (reverse (reverse xs) = xs) (reverseInvolutive xs) in Refl

map : (a -> b) -> (1 _ : List a) -> List b
map f [] = []
map f (x :: xs) = f x :: map f xs

mapCompose : {0 f : a -> b} -> {0 g : b -> c} -> (xs : List a) -> map (g . f) xs = map g (map f xs)
mapCompose [] = Refl
mapCompose (x :: xs) = rewrite mapCompose {f} {g} xs in Refl

mapAppend : {0 f : a -> b} -> (1 xs : List a) -> (0 ys : List a)
         -> map f (append xs ys) = append (map f xs) (map f ys)
mapAppend [] ys = Refl
mapAppend (x :: xs) ys = rewrite mapAppend {f} xs ys in Refl

data Tree a b = Leaf a | Node (Tree a b) b (Tree a b)

mapTree : (a -> c) -> (b -> d) -> Tree a b -> Tree c d
mapTree f g (Leaf x) = Leaf (f x)
mapTree f g (Node x y z) = Node (mapTree f g x) (g y) (mapTree f g z)

product : Num a => List a -> a
product = foldr (*) 1

foldrAppend : {0 f : a -> b -> b} -> {0 e : b} -> (xs, ys : List a)
           -> foldr f e (append xs ys) = foldr f (foldr f e ys) xs
foldrAppend [] ys = Refl
foldrAppend (x :: xs) ys = rewrite foldrAppend {f} {e} xs ys in Refl

foldrCons : (xs : List a) -> foldr (::) [] xs = xs
foldrCons [] = Refl
foldrCons (x :: xs) = rewrite foldrCons xs in Refl

foldrConsAppend : (xs, ys : List a) -> append xs ys = foldr (::) ys xs
foldrConsAppend xs ys =
  rewrite sym (foldrCons (append xs ys)) in
  rewrite foldrAppend {f = Prelude.(::)} {e = []} xs ys in
  rewrite foldrCons ys in Refl

mapFoldr : {0 f : a -> b} -> (xs : List a) -> map f xs = foldr (\ x, ys => f x :: ys) (the (List b) []) xs
mapFoldr [] = Refl
mapFoldr (x :: xs) = rewrite mapFoldr {f} xs in Refl

foldTree : (a -> c) -> (c -> b -> c -> c) -> Tree a b -> c
foldTree f g (Leaf x) = f x
foldTree f g (Node x y z) = g (foldTree f g x) y (foldTree f g z)

mapFoldTree : {0 f : a -> c} -> {0 g : b -> d} -> (t : Tree a b)
           -> mapTree f g t = foldTree (Leaf . f) (\ lt, b, rt => Node lt (g b) rt) t
mapFoldTree (Leaf x) = Refl
mapFoldTree (Node x y z) = rewrite mapFoldTree {f} {g} x in
                           rewrite mapFoldTree {f} {g} z in Refl

downFrom : Nat -> List Nat
downFrom Z = []
downFrom (S n) = n :: downFrom n

breakSum : {n : Nat} -> {l : List Nat} -> sum (n :: l) = n + sum l
breakSum {n} {l = []} = sym (zRightId n)
breakSum {n} {l = x :: l} = Calc $
  |~ sum (n :: x :: l)
  ~= foldl (+) 0 (n :: x :: l)
  ~= foldl (+) n (x :: l)
  ~= foldl (+) (n + x) l
  ~= sum (n + x :: l)
  ~~ (n + x) + sum l ...(breakSum)
  ~~ n + (x + sum l) ...(plusAssoc n x (sum l))
  ~~ n + (sum (x :: l)) ...(cong (n +) (sym breakSum))

sumDown : (n : Nat) -> sum (downFrom n) * 2 = n * (monus n 1)
sumDown 0 = Refl
sumDown (S n) = Calc $
  |~ sum (downFrom (S n)) * 2
  ~= sum (n :: downFrom n) * 2
  ~~ (n + sum (downFrom n)) * 2 ...(cong (*2) breakSum)
  ~~ n * 2 + sum (downFrom n) * 2 ...(multDistributesOverPlusLeft n (sum (downFrom n)) 2)
  ~~ n * 2 + n * monus n 1 ...(cong (n * 2 +) (sumDown n))
  ~~ (S n) * (monus (S n) 1) ...(case n of
    0 => the (0 * 2 + 0 * 0 = 1 * monus 1 1) Refl
    (S n') => Calc $
      |~ S n' * 2 + S n' * monus (S n') 1
      ~= S n' * 2 + S n' * n'
      ~~ S n' * (S (S n')) ...(sym $ multDistributesOverPlusRight (S n') 2 n')
      ~~ (S (S n')) * S n' ...(timesComm (S n') (S (S n')))
      ~= S n * monus (S n) 1)

record IsMonoid {0 a : Type} (0 op : a -> a -> a) (0 e : a) where
  constructor MkMonoid
  assoc : (x, y, z : a) -> op (op x y) z = op x (op y z)
  lIdentity : (x : a) -> op e x = x
  rIdentity : (x : a) -> op x e = x

plusMonoid : IsMonoid {a = Nat} (+) 0
plusMonoid = MkMonoid (\ x, y, z => sym (plusAssociative x y z)) (\x => Refl) plusZeroRightNeutral

multMonoid : IsMonoid {a = Nat} (*) 1
multMonoid = MkMonoid (\ x, y, z => sym (multAssociative x y z)) multOneLeftNeutral multOneRightNeutral

appendMonoid : IsMonoid {a = List b} (\ x, y => append x y) []
appendMonoid = MkMonoid appendAssoc (\x => Refl) appendRightId

foldrMonoid' : IsMonoid op e -> (0 ze : a) -> (xs : List a) -> (y : a) -> foldr op (op ze y) xs = op (foldr op ze xs) y
foldrMonoid' x ze [] y = Refl
foldrMonoid' x ze (z :: xs) y =
  rewrite foldrMonoid' x ze xs y in sym (assoc x z (foldr op ze xs) y)

foldrMonoid : {0 e : a} -> IsMonoid op e -> (xs : List a) -> (y : a) -> foldr op y xs = op (foldr op e xs) y
foldrMonoid x l y
  =       cong (\ z => foldr op z l) (sym $ lIdentity x y)
  `trans` foldrMonoid' x e l y

foldrMonoidAppend : {op : a -> a -> a} -> {e : a} -> IsMonoid op e -> (xs, ys : List a)
                 -> foldr op e (append xs ys) = op (foldr op e xs) (foldr op e ys)
foldrMonoidAppend x xs ys =
  rewrite foldrAppend {f = op} {e = e} xs ys in
  foldrMonoid x xs (foldr op e ys)

foldl' : (b -> a -> b) -> b -> List a -> b
foldl' op e [] = e
foldl' op e (x :: xs) = foldl' op (op e x) xs

foldlMonoid' : IsMonoid op e -> (0 ze : a) -> (xs : List a) -> (y : a)
            -> foldl op (op y ze) xs = op y (foldl op ze xs)
foldlMonoid' x ze [] y = Refl
foldlMonoid' x ze (w :: xs) y = rewrite assoc x y ze w in foldlMonoid' x (op ze w) xs y

foldlMonoid : IsMonoid op e -> (xs : List a) -> (y : a)
            -> foldl op y xs = op y (foldl op e xs)
foldlMonoid x l y
  =       cong (\ z => foldl op z l) (sym $ rIdentity x y)
  `trans` foldlMonoid' x e l y

foldrMonoidFoldl : IsMonoid op e -> (l : List a) -> foldr op e l = foldl op e l
foldrMonoidFoldl x [] = Refl
foldrMonoidFoldl x (y :: xs) =
  rewrite foldrMonoidFoldl x xs in
  rewrite sym $ foldlMonoid x xs y in
  rewrite lIdentity x y in Refl

Elem : (x : a) -> (xs : List a) -> Type
Elem x xs = Any (\ y => x = y) xs

allSplit : {0 P : a -> Type} -> (1 xs : List a) -> (0 ys : List a) -> All P (xs ++ ys) -> (All P xs, All P ys)
allSplit []  ys x = ([], x)
allSplit (y :: xs) ys (x :: z) = let prev = (allSplit xs ys z) in (x :: fst prev, snd prev)

allJoin : {0 P : a -> Type} -> (All P xs, All P ys) -> All P (xs ++ ys)
allJoin ([], y) = y
allJoin (x :: z, y) = x :: allJoin (z, y)

allAppend : {0 P : a -> Type} -> (xs : List a) -> (0 ys : List a) -> Iff (All P (xs ++ ys)) (All P xs, All P ys)
allAppend xs ys = MkIff (allSplit xs ys) allJoin

anySplit : {0 P : a -> Type} -> (1 xs : List a) -> Any P (xs ++ ys) -> Either (Any P xs) (Any P ys)
anySplit [] x = Right x
anySplit (_ :: xs) (Here x) = Left (Here x)
anySplit (_ :: xs) (There x) with (anySplit xs x)
  anySplit (_ :: xs) (There x) | (Left y) = Left (There y)
  anySplit (_ :: xs) (There x) | (Right y) = Right y

anyJoin : {0 P : a -> Type} -> (1 xs : List a) -> Either (Any P xs) (Any P ys) -> Any P (xs ++ ys)
anyJoin [] (Left x) impossible
anyJoin [] (Right x) = x
anyJoin (y :: xs) (Left (Here x)) = Here x
anyJoin (y :: xs) (Left (There x)) = There (anyJoin xs (Left x))
anyJoin (y :: xs) (Right x) = There (anyJoin xs (Right x))

anyAppend : {0 P : a -> Type} -> (xs : List a) -> (0 ys : List a) -> Iff (Any P (xs ++ ys)) (Either (Any P xs) (Any P ys))
anyAppend xs ys = MkIff (anySplit xs) (anyJoin xs)

pairEta : (w : (a,b)) -> (fst w, snd w) = w
pairEta (x, y) = Refl

jsIso : {0 P : a -> Type} -> (xs : List a) -> (0 ys : List a) -> (x : All P (xs ++ ys))
    -> Lists.allJoin (allSplit xs ys x) = x
jsIso [] ys x = Refl
jsIso (y :: xs) ys (x :: z) = rewrite pairEta (allSplit xs ys z) in rewrite jsIso xs ys z in Refl

sjIso : {0 P : a -> Type} -> (y : (All P xs, All P ys)) -> allSplit xs ys (allJoin y) = y
sjIso ([], y) = Refl
sjIso ((x :: z), y) = rewrite sjIso (z,y) in Refl

allAppendIso : {0 P : a -> Type} -> (xs : List a) -> (0 ys : List a) -> Iso (All P (xs ++ ys)) (All P xs, All P ys)
allAppendIso xs ys = MkIso (allSplit xs ys) allJoin (jsIso xs ys) sjIso

notAnyToAllNot : {0 P : a -> Type} -> (1 xs : List a) -> (Any P xs -> Void) -> All (\x => P x -> Void) xs
notAnyToAllNot [] f = []
notAnyToAllNot (x :: xs) f = (f . Here) :: notAnyToAllNot xs (f . There)

allNotToNotAny : {0 P : a -> Type} -> All (Not . P) xs -> Not (Any P xs)
allNotToNotAny [] (Here x) impossible
allNotToNotAny [] (There x) impossible
allNotToNotAny (x :: z) (Here y) = x y
allNotToNotAny (x :: z) (There y) = allNotToNotAny z y

notAnyId : FunExt => {0 P : a -> Type} -> {xs : List a} -> (x : Not (Any P xs)) -> allNotToNotAny (notAnyToAllNot xs x) = x
notAnyId x = funExt (\ z => case x z of {})

allNotId : {0 P : a -> Type} -> (y : All (\x => P x -> Void) xs) -> notAnyToAllNot xs (allNotToNotAny y) = y
allNotId [] = Refl
allNotId (x :: y) = rewrite allNotId y in Refl

notAnyIsoAllNot : FunExt => {0 P : a -> Type} -> (xs : List a) -> Iso (Not (Any P xs)) (All (Not . P) xs)
notAnyIsoAllNot xs = MkIso (notAnyToAllNot xs) allNotToNotAny notAnyId allNotId

anyNotToNotAll : {0 P : a -> Type} -> Any (Not . P) xs -> Not (All P xs)
anyNotToNotAll (Here x) (y :: _) = x y
anyNotToNotAll (There x) (y :: z) = anyNotToNotAll x z

-- This is equivalent to the weak excluded middle, which is not provable in intuitionistic logic.
notAllToAnyNotImpliesDeMorgan : ((a : Type) -> (xs : List a) -> {0 P : a -> Type} -> Not (All P xs) -> Any (Not . P) xs)
              -> (a : Type) -> (b : Type) -> Not (a,b) -> Either (Not a) (Not b)
notAllToAnyNotImpliesDeMorgan f a b g = case f Type {P = id} [a,b] (\ [x,y] => g (x,y)) of
  Here nota => Left nota
  There (Here notb) => Right notb

allToForall : {0 P : a -> Type} -> All P xs -> (x : a) -> Any (\y => x = y) xs -> P x
allToForall [] _ (Here y) impossible
allToForall [] _ (There y) impossible
allToForall (y :: _) _ (Here Refl) = y
allToForall (_ :: w) x (There z) = allToForall w x z

forallToAll : {0 P : (a -> Type)} -> {1 xs : List a} -> ((x : a) -> Any (\y => x = y) xs -> P x) -> All P xs
forallToAll {xs = []} f = []
forallToAll {xs = (x :: xs)} f = f x (Here Refl) :: forallToAll (\ y, z => f y (There z))

allForallId : {0 P : (a -> Type)} -> (x : All P xs) -> forallToAll (allToForall x) = x
allForallId [] = Refl
allForallId (x :: y) = rewrite the (forallToAll (\ y', z => allToForall y y' z) = y) (allForallId y) in Refl

forallAllId : FunExt => {0 P : (a -> Type)} -> {xs : List a} -> (y : ((x : a) -> Elem x xs -> P x)) -> allToForall (forallToAll y) = y
forallAllId {xs = []} y = funExt (\ x => funExt $ \ noWay => absurd noWay)
forallAllId {xs = (_ :: xs)} y = funExt (\ x => funExt $ \ elemxxs => case elemxxs of
  (Here Refl) => Refl
  (There z) => rewrite cong (\ f => f x z) (forallAllId {xs = xs} (\ y', z => y y' (There z))) in Refl
  )

allForallIso : FunExt => {0 P : a -> Type} -> {xs : List a} -> Iso (All P xs) ((x : a) -> Elem x xs -> P x)
allForallIso = MkIso allToForall forallToAll allForallId forallAllId

anyToExists : {0 P : a -> Type} -> (xs : List a) -> Any P xs -> (x : a ** (Any (\y => x = y) xs, P x))
anyToExists [] (Here x) impossible
anyToExists [] (There x) impossible
anyToExists (y :: xs) (Here x) = MkDPair y (Here Refl, x)
anyToExists (_ :: xs) (There x) with (anyToExists xs x)
  anyToExists (_ :: xs) (There x) | (MkDPair fst (y, z)) = MkDPair fst (There y, z)

existsToAny : {0 P : a -> Type} -> (x : a ** (Elem x xs, P x)) -> Any P xs
existsToAny (MkDPair fst (Here Refl, y)) = Here y
existsToAny (MkDPair fst (There x, y)) = There (existsToAny (MkDPair fst (x, y)))

anyExistsId : {0 P : a -> Type} -> {xs : List a} -> (x : Any P xs) -> existsToAny (anyToExists xs x) = x
anyExistsId {xs = _ :: _ } (Here x) = Refl
anyExistsId {xs = _ :: xs} (There x) = thereCase xs x `trans` cong There (anyExistsId x)
  where
    thereCase : (xs : List a) -> (x : Any P xs)
             -> existsToAny (anyToExists (_ :: xs) (There x)) = There (existsToAny (anyToExists xs x))
    thereCase xs x with (anyToExists xs x)
      thereCase xs x | (MkDPair fst (y, z)) = Refl

existsAnyId : {0 P : a -> Type} -> {xs : List a}
           -> (y : (x : a ** (Elem x xs, P x))) -> anyToExists xs (existsToAny y) = y
existsAnyId {xs = []} (MkDPair fst (There x, y)) impossible
existsAnyId (MkDPair fst (Here Refl, y)) = Refl
existsAnyId {xs = _ :: xs} (MkDPair fst (There x, y)) with (existsAnyId (the (DPair a (\ z => (Elem z xs, P z))) (MkDPair fst (x, y))))
  existsAnyId {xs = _ :: xs} (MkDPair fst (There x, y)) | with_pat with (anyToExists xs (existsToAny (the (DPair a (\ z => (Elem z xs, P z))) (MkDPair fst (x, y)))))
    existsAnyId {xs = _::xs} (MkDPair fst (There x, y)) | Refl | (MkDPair fst (x, y)) = Refl
anyExistsIso : {0 P : a -> Type} -> {xs : List a} -> Iso (Any P xs) (DPair a (\ x => (Elem x xs, P x)))
anyExistsIso = MkIso (anyToExists xs) existsToAny anyExistsId existsAnyId

Decidable : {a : Type} -> (p : a -> Type) -> Type
Decidable p = (x : a) -> Dec (p x)

allQ : {0 P : a -> Type} -> Decidable P -> Decidable (All P)
allQ f [] = Yes []
allQ f (x :: xs) with (f x)
  allQ f (x :: xs) | (No contra) = No (\ (x :: _) => contra x)
  allQ f (x :: xs) | (Yes prf) with (allQ f xs)
    allQ f (x :: xs) | (Yes prf) | (No contra) = No (\ (_ :: xs) => contra xs)
    allQ f (x :: xs) | (Yes prf) | (Yes y) = Yes (prf :: y)

anyQ : {0 P : a -> Type} -> Decidable P -> Decidable (Any P)
anyQ f [] = No absurd
anyQ f (x :: xs) with (f x)
  anyQ f (x :: xs) | (Yes prf) = Yes (Here prf)
  anyQ f (x :: xs) | (No contra) with (anyQ f xs)
    anyQ f (x :: xs) | (No contra) | (Yes prf) = Yes (There prf)
    anyQ f (x :: xs) | (No contra) | (No g) = No (\ x => case x of { Here a => contra a ; There as => g as })

data Merge : {a : Type} -> (xs, ys, zs : List a) -> Type where
  Empty : Merge [] [] []
  LeftMerge  : Merge xs ys zs -> Merge (x :: xs) ys (x :: zs)
  RightMerge : Merge xs ys zs -> Merge xs (y :: ys) (y :: zs)

split : {0 P : a -> Type} -> Decidable P -> (zs : List a)
     -> (xs : List a ** ys : List a ** (Merge xs ys zs, All P xs, All (Not . P) ys))
split f [] = ([] ** [] ** (Empty, [], []))
split f (z :: zs) with (Lists.split f zs)
  split f (z :: zs) | (xs ** (ys ** (merge, allxs, allys))) with (f z)
    split f (z :: zs) | (xs ** (ys ** (merge, allxs, allys))) | (Yes prf) = (z :: xs ** (ys ** (LeftMerge merge, prf :: allxs, allys)))
    split f (z :: zs) | (xs ** (ys ** (merge, allxs, allys))) | (No contra) = (xs ** (z :: ys ** (RightMerge merge, allxs, contra :: allys)))

