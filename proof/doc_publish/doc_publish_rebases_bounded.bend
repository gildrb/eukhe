# eukhe: the proof of LAW doc_publish_rebases_bounded
#
# PROOF: the version is not the base (other), so the re-read meets other
# bytes; no rebase is left (spent: the code's bound is the spec's 3), so
# the code refuses, and the run ends refused (dpb.done). A version equal to
# the base, or a rebase left, contradicts a premise.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S
import ../base/staging.bend as LStg
import ./base.bend as LA

def dpd.left(ls: List<&2, S.Reread>, +n: Nat, +b: Nat, +c: Nat, +v: Nat, lt: Bool, r: Maybe<&2, Nat>, hl: {Nat.is_lt(n, Dp.bound()) == lt : Bool}, spent: {Nat.is_lt(n, S.bound()) == False{} : Bool}) -> {DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step.moved(lt), b, c, Some{v}, r)) == S.Refused{} : S.Run}:
  match lt:
    case True{}:
      LStg.stg.absurd({DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step.moved(True{}), b, c, Some{v}, r)) == S.Refused{} : S.Run}, Equal.trans(Bool, True{}, Nat.is_lt(n, S.bound()), False{}, Equal.sym(Bool, Nat.is_lt(n, S.bound()), True{}, hl), spent))
    case False{}:
      LA.dpb.done(ls, 1n+n, S.Refused{})

def dpd.eq(ls: List<&2, S.Reread>, +n: Nat, +b: Nat, +c: Nat, +v: Nat, r: Maybe<&2, Nat>, e: Bool, h: {Nat.is_eq(v, b) == e : Bool}, spent: {Nat.is_lt(n, S.bound()) == False{} : Bool}, other: {Nat.is_eq(v, b) == False{} : Bool}) -> {DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(e)), b, c, Some{v}, r)) == S.Refused{} : S.Run}:
  match e:
    case True{}:
      LStg.stg.absurd({DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(True{})), b, c, Some{v}, r)) == S.Refused{} : S.Run}, Equal.trans(Bool, True{}, Nat.is_eq(v, b), False{}, Equal.sym(Bool, Nat.is_eq(v, b), True{}, h), other))
    case False{}:
      dpd.left(ls, n, b, c, v, Nat.is_lt(n, Dp.bound()), r, {==}, spent)

def DocPublish.doc_publish_rebases_bounded(n, b, c, v, r, ls, spent, other):
  dpd.eq(ls, n, b, c, v, r, Nat.is_eq(v, b), {==}, spent, other)
