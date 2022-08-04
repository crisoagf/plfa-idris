module Substitution

import Untyped
import Quantifiers
import Syntax.PreorderReasoning

public export
Rename : (0 ctx, ctx' : Context) -> Type
Rename ctx ctx' = ({0 a : LambdaType} -> ctx `Has` a -> ctx' `Has` a)

public export
Subst1 : (0 ctx, ctx' : Context) -> (0 a : LambdaType) -> Type
Subst1 ctx ctx' a = ctx `Has` a -> ctx' |- a

public export
Subst : (0 ctx, ctx' : Context) -> Type
Subst ctx ctx' = ({0 a : LambdaType} -> Subst1 ctx ctx' a)

public export
ids : Subst ctx ctx
ids x = Var x

shift : {0 a : LambdaType} -> Subst ctx (ctx :: a)
shift {a} x = Var (S x)

public export
cons : ctx' |- b -> Subst ctx ctx' -> Subst (ctx :: b) ctx'
cons {a = a} x f Z = x
cons {a = a} x f (S y) = f y

public export
seq : Subst ctx ctx' -> Subst ctx' ctx'' -> Subst ctx ctx''
seq f g = subst g . f

ren : Rename ctx ctx' -> Subst ctx ctx'
ren f = ids . f

subHead : {0 sigma : Subst _ _} -> subst (cons m sigma) (Var Z) = m
subHead = Refl

subTail
   : {auto extn : Extensionality}
  -> {sigma : Subst _ _} -> {m : _} -> Substitution.shift `seq` cons m sigma = sigma
subTail = extn $ \ v => subTail_rhs v
  where
    subTail_rhs : (v : _) -> (Substitution.shift `seq` cons m sigma) v = sigma v
    subTail_rhs v = case v of
                         Z => Refl
                         (S x) => Refl

subEta
   : {auto extn : Extensionality}
  -> {sigma : Subst _ _} -> (cons (subst sigma (Var Z)) (Substitution.shift `seq` sigma)) = sigma
subEta = extn $ \ v => lemma v
  where lemma : (v : _) -> (cons (subst sigma (Var Z)) (Substitution.shift `seq` sigma)) v = sigma v
        lemma Z = Refl
        lemma (S x) = Refl

zShift : {auto extn : Extensionality}
      -> cons (Var Z) Substitution.shift = Substitution.ids
zShift = extn lemma
  where lemma : (v : _) -> cons (Var Z) Substitution.shift v = Substitution.ids v
        lemma Z = Refl
        lemma (S x) = Refl

subIdL : {sigma : Subst _ _} -> {auto extn : Extensionality} -> Substitution.ids `seq` sigma = sigma
subIdL = extn $ \ _ => Refl

subDist : {sigma : Subst _ _} -> {tau : Subst _ _} -> {m : _}
       -> {auto extn : Extensionality}
       -> cons m sigma `seq` tau = (cons (subst tau m) (sigma `seq` tau))
subDist = extn lemma
  where lemma : (v : _) -> (cons m sigma `seq` tau) v = cons (subst tau m) (sigma `seq` tau) v
        lemma Z = Refl
        lemma (S x) = Refl

subApp : {sigma : Subst _ _} 
      -> subst sigma (l `App` m) = subst sigma l `App` subst sigma m
subApp = Refl

congExt : {rho, rho' : Rename _ _}
       -> {auto extn : Extensionality}
       -> ({0 a : LambdaType} -> rho {a} = rho' {a})
       -> {0 a : LambdaType} -> ext rho {b = b} = ext rho' {a}
congExt rr' = extn lemma
  where lemma : (v : _) -> ext rho v = ext rho' v
        lemma Z = Refl
        lemma (S x) = cong (S . ($ x)) rr'


congRename : {rho, rho' : Rename _ _} -> {m : _}
       -> {auto extn : Extensionality}
       -> ({0 a : LambdaType} -> rho {a} = rho' {a})
       -> rename rho m = rename rho' m
congRename {m = (Var x)} rr' = cong (Var . ($ x)) rr'
congRename {m = (Lam x)} rr' = cong Lam (congRename $ congExt rr')
congRename {m = (x `App` y)} rr' = cong2 App (congRename rr') (congRename rr')

congExts : {sigma, sigma' : Subst _ _}
       -> {auto extn : Extensionality}
       -> ({0 a : LambdaType} -> sigma {a} = sigma' {a})
       -> {0 a : LambdaType} -> exts sigma = exts sigma' {a}
congExts ss' = extn lemma
  where lemma : (v : _) -> exts sigma v = exts sigma' v
        lemma Z = Refl
        lemma (S x) = cong (rename S . ($ x)) ss'

congSub : {sigma, sigma' : Subst _ _} -> {m, m' : _}
       -> {auto extn : Extensionality}
       -> ({0 a : LambdaType} -> sigma {a} = sigma' {a})
       -> m = m'
       -> subst sigma m = subst sigma' m'
congSub {m = (Var x)} ss' Refl = cong ($ x) ss'
congSub {m = (Lam x)} {m' = (Lam x)} ss' Refl = cong Lam $ congSub (congExts ss') Refl
congSub {m = (x `App` y)} ss' Refl = cong2 App (congSub ss' Refl) (congSub ss' Refl)

congSubZero : {m, m' : _}
           -> {auto extn : Extensionality}
           -> m = m'
           -> {0 a : LambdaType} -> (substZero m = substZero m' {a})
congSubZero Refl = extn (\_ => Refl)

congCons : {m, n : delta |- _} -> {sigma, tau : Subst _ delta}
        -> {auto extn : Extensionality}
        -> m = n -> ({0 a : _} -> sigma {a} = tau {a})
        -> cons m sigma = cons n tau
congCons {m} {n = m} Refl g = extn lemma
  where lemma : (v : _) -> cons m sigma v = cons m tau v
        lemma Z = Refl
        lemma (S x) = cong ($ x) g

congSeq : {sigma, sigma' : Subst _ delta} -> {tau, tau' : Subst delta _}
       -> {auto extn : Extensionality}
       -> ({0 a : _} -> sigma {a} = sigma' {a})
       -> ({0 a : _} -> tau {a} = tau' {a})
       -> {0 a : _} -> (sigma `seq` tau) {a} = (sigma' `seq` tau') {a}
congSeq ss' tt' = extn lemma
  where lemma : (v : _) -> (sigma `seq` tau) v = (sigma' `seq` tau') v
        lemma v = Calc $
          |~ (subst tau (sigma v))
          ~~ subst tau' (sigma v) ...(congSub tt' Refl)
          ~~ subst tau' (sigma' v) ...(cong (subst tau' . ($ v)) ss')

renExt : {rho : Rename _ _}
      -> {auto extn : Extensionality}
      -> ren (ext rho) = exts (ren rho)
renExt = extn lemma
  where lemma : (v : _) -> ren (Untyped.ext rho) v = exts (ren rho) v
        lemma Z = Refl
        lemma (S x) = Refl

renameSubstRen
   : {rho : Rename _ _}
  -> {m : _}
  -> {auto extn : Extensionality}
  -> rename rho m = subst (ren rho) m
renameSubstRen {m = (Var x)} = Refl
renameSubstRen {m = (Lam x)} = Calc $
  |~ Lam (rename (Untyped.ext rho) x)
  ~~ Lam (subst (ren (Untyped.ext rho)) x) ...(cong Lam renameSubstRen)
  ~~ Lam (subst (exts (ren rho)) x) ...(cong Lam (congSub renExt Refl))
renameSubstRen {m = (x `App` y)} = cong2 App renameSubstRen renameSubstRen

renShift : {auto extn : Extensionality} -> ren S = Substitution.shift
renShift = extn lemma
  where lemma : (v : _) -> ren S v = Substitution.shift v
        lemma Z = Refl
        lemma (S x) = Refl

renameShift : {auto extn : Extensionality} -> rename S m = subst Substitution.shift m
renameShift = Calc $
  |~ rename S m
  ~~ subst (ren S) m ...(renameSubstRen)
  ~~ subst shift m ...(congSub renShift Refl)

extsConsShift : {sigma : Subst _ _}
  -> { auto extn : Extensionality }
  -> {0 a, b : _}
  -> exts sigma {a} {b} = cons (Var Z) (sigma `seq` Substitution.shift)
extsConsShift = extn (\ x => case x of { Z => Refl; S x => renameSubstRen})

extConsZShift : {rho : Rename _ _}
  -> {auto extn : Extensionality}
  -> ren (ext rho) = (cons (Var Z) (ren rho `seq` Substitution.shift))
extConsZShift = Calc $
  |~ ren (ext rho)
  ~~ exts (ren rho) ...(renExt)
  ~~ cons (Var Z) (ren rho `seq` Substitution.shift) ...(extsConsShift)

substZConsIds : {auto extn : Extensionality} -> {m : _ |- b} -> {0 a : _} -> substZero m = cons m Substitution.ids {a}
substZConsIds = extn lemma
  where lemma : (v : _) -> substZero m v = cons m Substitution.ids v
        lemma Z = Refl
        lemma (S x) = Refl

subAbs : {auto extn : Extensionality} -> {sigma : Subst _ _}
  -> subst sigma (Lam n) = Lam (subst (cons (Var Z) (sigma `seq` Substitution.shift)) n)
subAbs = Calc $
  |~ Lam (subst (exts sigma) n) 
  ~~ Lam (subst (cons (Var Z) (sigma `seq` shift)) n) ...(cong Lam $ congSub extsConsShift Refl)

extsIds : {auto extn : Extensionality} -> exts Substitution.ids = Substitution.ids
extsIds = extn lemma
  where lemma : (v : _) -> exts Substitution.ids v = Substitution.ids v
        lemma Z = Refl
        lemma (S x) = Refl

public export
subId : {auto extn : Extensionality} -> {m : _} -> subst Substitution.ids m = m
subId {m = (Var x)} = Refl
subId {m = (x `App` y)} = cong2 App subId subId
subId {m = (Lam x)} = cong Lam $ congSub extsIds Refl `trans` subId

public export
renameId : {auto extn : Extensionality} -> {m : _} -> rename Basics.id m = m
renameId = renameSubstRen `trans` subId

subIdR : {auto extn : Extensionality} -> {sigma : Subst _ _} -> (sigma `seq` Substitution.ids) = sigma
subIdR = extn (\ _ => subId)

composeExt : {auto extn : Extensionality}
          -> {rho : Rename delta _} -> {rho' : Rename _ delta}
          -> ext rho . ext rho' = ext (rho . rho')
composeExt = extn lemma
  where lemma : (v : _) -> ext rho (ext rho' v) = ext (rho . rho') v
        lemma Z = Refl
        lemma (S x) = Refl

composeRename : {auto extn : Extensionality}
          -> {rho : Rename delta _} -> {rho' : Rename _ delta}
          -> {m : _}
          -> rename rho (rename rho' m) = rename (rho . rho') m
composeRename {m = (Var x)} = Refl
composeRename {m = (x `App` y)} = cong2 App composeRename composeRename
composeRename {m = (Lam x)} = cong Lam . Calc $
  |~ rename (ext rho) (rename (ext rho') x)
  ~~ rename (ext rho . ext rho') x ...(composeRename)
  ~~ rename (ext (rho . rho')) x ...(congRename composeExt)

commuteSubstRename
   : {auto extn : Extensionality}
  -> {m : _ |- Star} -> {sigma : Subst _ _}
  -> {rho : {ctx : _} -> Rename ctx (ctx :: Star)}
  -> ({x : _ `Has` Star} -> exts sigma (rho x) = rename rho (sigma x))
  -> subst (exts sigma) (rename rho m) = rename rho (subst sigma m)
commuteSubstRename {m = (Var x)} f = f
commuteSubstRename {m = (x `App` y)} f
  = cong2 App (commuteSubstRename {rho = rho} f) (commuteSubstRename {rho = rho} f)
commuteSubstRename {m = (Lam x)} f = cong Lam (commuteSubstRename {rho = rho'} h)
  where
    rho' : {ctx : _} -> Rename ctx (ctx :: Star)
    rho' {ctx = Empty} = \ x => case x of {}
    rho' {ctx = (y :: Star)} = ext rho

    h : {x : _ :: Star `Has` Star} -> exts (exts sigma) (ext rho x) = rename (ext rho) (exts sigma x)
    h {x = Z} = Refl
    h {x = S y} = Calc $
      |~ rename S (exts sigma (rho y))
      ~~ rename S (rename rho (sigma y)) ...(cong (rename S) f)
      ~~ rename (S . rho) (sigma y) ...(composeRename)
      ~~ rename (ext rho . S) (sigma y) ...(congRename Refl)
      ~~ rename (ext rho) (rename S (sigma y)) ...(sym composeRename)

extsSeq
   : {auto extn : Extensionality}
  -> {sigma1 : Subst _ delta}
  -> {sigma2 : Subst delta _}
  -> {a : LambdaType} -> (exts sigma1 `seq` exts sigma2) {a} = exts (sigma1 `seq` sigma2)
extsSeq = extn lemma
   where lemma : {a : _} -> (v : _ :: b `Has` a) -> (exts sigma1 `seq` exts sigma2) v = exts (sigma1 `seq` sigma2) v
         lemma Z = Refl
         lemma {a = Star} {b = Star} (S x) = commuteSubstRename {rho = S} Refl

public export
subSub
   : {auto extn : Extensionality}
  -> {sigma1 : Subst _ delta}
  -> {sigma2 : Subst delta _}
  -> {m : ctx |- a}
  -> (subst sigma2 (subst sigma1 m)) = subst (sigma1 `seq` sigma2) m
subSub {m = (Var x)} = Refl
subSub {m = (x `App` y)} = cong2 App subSub subSub
subSub {m = (Lam x)} {ctx} = cong Lam (subSub {m = x} {sigma1 = exts sigma1} `trans` congSub extsSeq Refl)

renameSubst : {auto extn : Extensionality}
           -> {rho : Rename gamma delta} -> {sigma : Subst delta _}
           -> subst sigma (rename rho m) = subst ( sigma . rho ) m
renameSubst = cong (subst sigma) renameSubstRen `trans` subSub

subAssoc : {auto extn : Extensionality}
        -> {sigma : Subst gamma delta}
        -> {tau : Subst delta epsilon}
        -> {theta : Subst epsilon zeta}
        -> {0 a : LambdaType}
        -> ((sigma `seq` tau) `seq` theta) {a} = sigma `seq` (tau `seq` theta)
subAssoc = extn lemma
  where
    lemma : (v : _) -> ((sigma `seq` tau) `seq` theta) v = (sigma `seq` (tau `seq` theta)) v
    lemma _ = subSub

public export
substZeroExtsCons : {auto extn : Extensionality}
                 -> {sigma : Subst gamma delta} -> {m : delta |- b}
                 -> {0 a : _}
                 -> (exts sigma `seq` substZero m) {a} = cons m sigma
substZeroExtsCons = Calc $
  |~ (exts sigma `seq` substZero m)
  ~~ (cons (Var Z) (sigma `seq` shift) `seq` cons m ids) ...(congSeq (extsConsShift {sigma = sigma}) substZConsIds)
  ~~ (cons (subst (cons m ids) (Var Z)) ((sigma `seq` shift) `seq` cons m ids)) ...(subDist)
  ~~ (cons m (sigma `seq` (shift `seq` cons m ids))) ...(congCons (subHead {sigma = ids}) (subAssoc {sigma = sigma}))
  ~~ (cons m (sigma `seq` ids)) ...(congCons Refl (congSeq {sigma = sigma} Refl (subTail {sigma = ids} {m})))
  ~~ cons m sigma ...(congCons Refl (subIdR {sigma = sigma}))

public export
substCommute : {auto extn : Extensionality}
            -> {n : ctx :: Star |- Star} -> {m : ctx |- Star} -> {sigma : Subst ctx ctx'}
            -> replace (subst (exts sigma) n) (subst sigma m) = subst sigma (replace n m)
substCommute = Calc $
  |~ replace (subst (exts sigma) n) (subst sigma m)
  ~~ subst (substZero (subst sigma m)) (subst (exts sigma) n) ...(Refl)
  ~~ subst (cons (subst sigma m) ids) (subst (exts sigma) n) ...(congSub substZConsIds Refl)
  ~~ subst (exts sigma `seq` cons (subst sigma m) ids) n ...(subSub)
  ~~ subst (cons (Var Z) (sigma `seq` shift) `seq` cons (subst sigma m) ids) n ...(congSub (congSeq (extsConsShift {sigma}) Refl) Refl)
  ~~ subst (cons (subst (cons (subst sigma m) ids) (Var Z)) ((sigma `seq` shift) `seq` cons (subst sigma m) ids)) n ...(congSub subDist Refl)
  ~~ subst (cons (subst sigma m) (sigma `seq` (shift `seq` cons (subst sigma m) ids))) n ...(congSub (congCons (subHead {sigma}) (subAssoc {sigma})) Refl)
  ~~ subst (cons (subst sigma m) (sigma `seq` ids)) n ...(congSub (congCons Refl (congSeq {sigma} Refl (subTail {m = subst sigma m} {sigma = ids}))) Refl)
  ~~ subst (cons (subst sigma m) sigma) n ...(congSub (congCons Refl (subIdR {sigma = sigma})) Refl)
  ~~ subst (cons (subst sigma m) (ids `seq` sigma)) n ...(congSub (congCons Refl (subIdL {sigma = sigma})) Refl)
  ~~ subst (cons m ids `seq` sigma) n ...(congSub (sym subDist) Refl)
  ~~ subst (substZero m `seq` sigma) n ...(congSub (congSeq (sym (substZConsIds {m})) Refl) Refl)
  ~~ subst sigma (subst (substZero m) n) ...(sym (subSub {sigma1 = substZero m} {sigma2 = sigma}))
  ~~ subst sigma (replace n m) ...(Refl)

public export
renameSubstCommute : {auto extn : Extensionality}
            -> {n : ctx :: Star |- Star} -> {m : ctx |- Star} -> {rho : Rename ctx ctx'}
            -> replace (rename (ext rho) n) (rename rho m) = rename rho (replace n m)
renameSubstCommute = Calc $
  |~ replace (rename (ext rho) n) (rename rho m)
  ~~ replace (subst (ren (ext rho)) n) (subst (ren rho) m) ...(congSub (congSubZero renameSubstRen) renameSubstRen)
  ~~ replace (subst (exts (ren rho)) n) (subst (ren rho) m) ...(congSub Refl (congSub renExt Refl))
  ~~ subst (ren rho) (replace n m) ...(substCommute)
  ~~ rename rho (replace n m) ...(sym renameSubstRen)

replaceSkip : (m : (ctx :: a) :: b |- c) -> (n : ctx |- a) -> ctx :: b |- c
replaceSkip m n = subst (exts (substZero n)) m

public export
substitution : {auto extn : Extensionality}
            -> {m : (ctx :: Star) :: Star |- Star} -> {n : ctx :: Star |- Star} -> {l : ctx |- Star}
            -> replace (replace m n) l = replace (replaceSkip m l) (replace n l)
substitution = sym substCommute
