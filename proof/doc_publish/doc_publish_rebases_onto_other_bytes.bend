# eukhe: the proof of LAW doc_publish_rebases_onto_other_bytes
#
# PROOF: the version is not the base (other), so the re-read meets other
# bytes; rebases are left (left: the code's bound is the spec's 3), so the
# code rebases, and the run goes on based on the version with the rebased
# change. A version equal to the base, or no rebase left, contradicts a
# premise.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S
import ../base/staging.bend as LStg

def dpr.left(ls: List<&2, S.Reread>, +n: Nat, +b: Nat, +c: Nat, +v: Nat, +x: Nat, lt: Bool, hl: {Nat.is_lt(n, Dp.bound()) == lt : Bool}, left: {Nat.is_lt(n, S.bound()) == True{} : Bool}) -> {DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step.moved(lt), b, c, Some{v}, Some{x})) == DocPublish.sp_run(ls, 1n+n, DocPublish.Going{v, x}) : S.Run}:
  match lt:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurd({DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step.moved(False{}), b, c, Some{v}, Some{x})) == DocPublish.sp_run(ls, 1n+n, DocPublish.Going{v, x}) : S.Run}, Equal.trans(Bool, True{}, Nat.is_lt(n, S.bound()), False{}, Equal.sym(Bool, Nat.is_lt(n, S.bound()), True{}, left), hl))

def dpr.eq(ls: List<&2, S.Reread>, +n: Nat, +b: Nat, +c: Nat, +v: Nat, +x: Nat, e: Bool, h: {Nat.is_eq(v, b) == e : Bool}, left: {Nat.is_lt(n, S.bound()) == True{} : Bool}, other: {Nat.is_eq(v, b) == False{} : Bool}) -> {DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(e)), b, c, Some{v}, Some{x})) == DocPublish.sp_run(ls, 1n+n, DocPublish.Going{v, x}) : S.Run}:
  match e:
    case True{}:
      LStg.stg.absurd({DocPublish.sp_run(ls, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen.of(True{})), b, c, Some{v}, Some{x})) == DocPublish.sp_run(ls, 1n+n, DocPublish.Going{v, x}) : S.Run}, Equal.trans(Bool, True{}, Nat.is_eq(v, b), False{}, Equal.sym(Bool, Nat.is_eq(v, b), True{}, h), other))
    case False{}:
      dpr.left(ls, n, b, c, v, x, Nat.is_lt(n, Dp.bound()), {==}, left)

def DocPublish.doc_publish_rebases_onto_other_bytes(n, b, c, v, x, ls, left, other):
  dpr.eq(ls, n, b, c, v, x, Nat.is_eq(v, b), {==}, left, other)
