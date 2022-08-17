module Book.Part1.Isomorphism
import Book.Part1.Naturals
import Book.Part1.Induction
import Book.Part1.Relations
import Control.Order
import Control.Relation

public export
record Iso (a : Type) (b : Type) where
  constructor MkIso
  to : a -> b
  from : b -> a
  fromTo : (x : a) -> from (to x) = x
  toFrom : (y : b) -> to (from y) = y

export
isoRefl : Iso a a
isoRefl = MkIso (\x => x) (\x => x) (\x => Refl) (\y => Refl)

export
isoSym : Iso a b -> Iso b a
isoSym (MkIso to from fromTo toFrom) = MkIso from to toFrom fromTo

export
isoTrans : Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso to from fromTo toFrom) (MkIso f g fromTo1 toFrom1) = MkIso (f . to) (from . g) (\ a => cong from (fromTo1 (to a)) `trans` fromTo a) (\ c => cong f (toFrom (g c)) `trans` toFrom1 c)

Transitive Type Iso where
  transitive = isoTrans

Reflexive Type Iso where
  reflexive  = isoRefl

export
Preorder Type Iso where

public export
record Embedding (a : Type) (b : Type) where
  constructor MkEmbed
  to : a -> b
  from : b -> a
  fromTo : (x : a) -> from (to x) = x

embeddingRefl : Embedding a a
embeddingRefl = MkEmbed (\x => x) (\x => x) (\x => Refl)

embeddingTrans : Embedding a b -> Embedding b c -> Embedding a c
embeddingTrans (MkEmbed to from fromTo) (MkEmbed f g fromTo1) = MkEmbed (f . to) (from . g) (\ a => cong from (fromTo1 (to a)) `trans` fromTo a)

infixr 4 `trans`

embeddingAntiSym : (aToB : Embedding a b) -> (bToA : Embedding b a) -> aToB.from = bToA.to -> aToB.to = bToA.from -> Iso a b
embeddingAntiSym (MkEmbed to from fromTo) (MkEmbed f g fromTo1) fromEqTo toEqFrom
  = MkIso
    to
    from
    fromTo
    (\ b =>   cong (\ f => to (f b)) fromEqTo
      `trans` cong (\ g => g  (f b)) toEqFrom
      `trans` fromTo1 b
    )

stepEmbed : (0 a : Type) -> Embedding a b -> Embedding b c -> Embedding a c
stepEmbed _ = embeddingTrans

qedEmbed : (0 a : Type) -> Embedding a a
qedEmbed _ = embeddingRefl

isoImpliesEmbed : Iso a b -> Embedding a b
isoImpliesEmbed (MkIso to from fromTo toFrom) = MkEmbed to from fromTo

public export
record Iff (a : Type) (b : Type) where
  constructor MkIff
  to : a -> b
  from : b -> a

iffRefl : Iff a a
iffRefl = MkIff (\x => x) (\x => x)

iffSym : Iff a b -> Iff b a
iffSym (MkIff to from) = MkIff from to

iffTrans : Iff a b -> Iff b c -> Iff a c
iffTrans (MkIff to from) (MkIff f g) = MkIff (\x => f (to x)) (\x => from (g x))

binEmbedding : Embedding Nat Bin
binEmbedding = MkEmbed to from (\ x => fromToId x)

-- Check out "notToFromId" in Induction
