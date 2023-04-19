module Book.Part3.ContextualEquivalence

import Book.Part2.BigStep
import Book.Part2.Untyped
import Book.Part3.Denotational
import Book.Part3.Compositional
import Book.Part3.Soundness2
import Book.Part3.Adequacy
import Control.Function.FunExt

terminates : {ctx : _} -> (m : ctx |- Star) -> Type
terminates {ctx} m = (n : (ctx :< Star |- Star) ** m -=>> Lam n)

(==) : {ctx : _} -> (m, n : ctx |- Star) -> Type
(==) {ctx} m n = {c : Ctx ctx Empty} -> terminates (plug c m) `iff` terminates (plug c n)

denotEqualTerminates : FunExt => {0 ctx : _} -> {m, n : ctx |- Star} -> {c : Ctx ctx Empty}
                    -> Denote m == Denote n -> terminates (plug c m)
                    -> terminates (plug c n)
denotEqualTerminates denoteMEqDenoteN (n' ** cmToLamN') =
  let
    denoteCmEqDenoteLamN' = soundness cmToLamN'
    denoteCmEqDenoteCn    = compositionality denoteMEqDenoteN
    denoteCnEqDenoteLamN' = sym denoteCmEqDenoteCn `trans`denoteCmEqDenoteLamN'
    judgeCn = denoteImpliesJudge denoteCnEqDenoteLamN' in
      cbnReduce (snd (snd (snd judgeCn)))

denotEqualContexEqual : FunExt => {m, n : ctx |- Star} -> Denote m == Denote n -> m == n
denotEqualContexEqual eq = (\ tm => denotEqualTerminates eq tm , \ tn => denotEqualTerminates (sym eq) tn)

