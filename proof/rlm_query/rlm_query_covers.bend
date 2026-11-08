# eukhe: the proof of LAW rlm_query_covers
#
# PROOF: an admitted plan is the spec's waves (qp.admitted), which add up to the batch (qw.sum: the code's loop counts each call once, qw.sum_go).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def cv.go(+r: Nat, +c: Nat, +w: Nat, +sizes: List<&2, Nat>, +ws: List<&2, Nat>, adm: {ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}) -> {QSpec.total(ws) == List.length(&2, Nat, sizes) : Nat}:
  (ews, hr) = adm
  %Equal.sym(List<&2, Nat>, ws, QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))), ews) : {QSpec.total(_) == List.length(&2, Nat, sizes) : Nat}
  LP.qw.sum(QSpec.wave(w, Nat.sub(c, r)), List.length(&2, Nat, sizes))

def RlmQuery.rlm_query_covers(r, c, w, b, u, sizes, ws, e):
  cv.go(r, c, w, sizes, ws, LP.qp.admitted(r, c, w, b, u, sizes, ws, e))
