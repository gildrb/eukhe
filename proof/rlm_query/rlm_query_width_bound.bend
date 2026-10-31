# eukhe: the proof of LAW rlm_query_width_bound
#
# PROOF: an admitted plan is the spec's waves of k = the wave of the room, r below c (qp.admitted); every wave is at most k (qw.waves) and k at most the width given (qw.k_width).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def wb.go(+r: Nat, +c: Nat, +p: Nat, +sizes: List<&2, Nat>, +ws: List<&2, Nat>, adm: {ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(1n+p, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}) -> {RlmQuery.rq_narrow(1n+p, ws) == True{} : Bool}:
  (ews, hr) = adm
  +k = QSpec.wave(1n+p, Nat.sub(c, r))
  %Equal.sym(List<&2, Nat>, ws, QSpec.waves(List.length(&2, Nat, sizes), k), ews) : {RlmQuery.rq_narrow(1n+p, _) == True{} : Bool}
  LP.qw.narrow(QSpec.waves(List.length(&2, Nat, sizes), k), 1n+p, k, LP.qw.waves(k, List.length(&2, Nat, sizes), LP.qw.k_pos(1n+p, Nat.sub(c, r), LN.rq.sub_pos(r, c, hr))), LP.qw.k_width(p, Nat.sub(c, r)))

def RlmQuery.rlm_query_width_bound(r, c, w, b, u, sizes, ws, set, e):
  match w:
    case 0n:
      LN.rq.absurd({RlmQuery.rq_narrow(0n, ws) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, set))
    case 1n++p:
      wb.go(r, c, p, sizes, ws, LP.qp.admitted(r, c, 1n+p, b, u, sizes, ws, e))
