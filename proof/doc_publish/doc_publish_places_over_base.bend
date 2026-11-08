# eukhe: the proof of LAW doc_publish_places_over_base
#
# PROOF: the base equals itself (dpb.eq_refl), so the re-read meets the
# base and the code places the change; the run then ends, whatever
# re-reads are left (dpb.done).

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S
import ../base/staging.bend as LStg
import ./base.bend as LA

def dpp.eq(ls: List<&2, S.Reread>, +n: Nat, +b: Nat, +c: Nat, r: Maybe<&2, Nat>, e: Bool, h: {Nat.is_eq(b, b) == e : Bool}) -> {DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(e)), b, c, Some{b}, r)) == S.Wrote{Some{b}, b, c} : S.Run}:
  match e:
    case True{}:
      LA.dpb.done(ls, 1n+n, S.Wrote{Some{b}, b, c})
    case False{}:
      LStg.stg.absurd({DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(False{})), b, c, Some{b}, r)) == S.Wrote{Some{b}, b, c} : S.Run}, Equal.trans(Bool, True{}, Nat.is_eq(b, b), False{}, Equal.sym(Bool, Nat.is_eq(b, b), True{}, LA.dpb.eq_refl(b)), h))

def DocPublish.doc_publish_places_over_base(n, b, c, r, ls):
  dpp.eq(ls, n, b, c, r, Nat.is_eq(b, b), {==})
