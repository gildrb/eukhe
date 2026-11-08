# eukhe: lemmas shared by the proofs of area doc_publish: a run that
# ended stays ended, and Nat equality is reflexive

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S

def dpb.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      dpb.eq_refl(p)

# a run that ended answers its end, whatever re-reads are left
def dpb.done(ls: List<&2, S.Reread>, +n: Nat, r: S.Run) -> {DocPublish.sp_run(ls, n, DocPublish.Ended{r}) == r : S.Run}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match l:
        case S.Reread{d, x}:
          {==}
