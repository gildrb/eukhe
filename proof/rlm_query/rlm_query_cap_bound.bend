# eukhe: the proof of LAW rlm_query_cap_bound
#
# PROOF: an admitted plan is the spec's waves of k = the wave of the room c - r, with r below c (qp.admitted); the room is positive, so every wave holds a call and at most k (qw.waves), k is within the room (qw.k_room), so r plus a wave is within c (qw.capped).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def cb.go(+r: Nat, +c: Nat, +w: Nat, +sizes: List<&2, Nat>, +ws: List<&2, Nat>, adm: {ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}) -> {RlmQuery.rq_capped(r, c, ws) == True{} : Bool}:
  (ews, hr) = adm
  +hr2 = hr
  +k = QSpec.wave(w, Nat.sub(c, r))
  %Equal.sym(List<&2, Nat>, ws, QSpec.waves(List.length(&2, Nat, sizes), k), ews) : {RlmQuery.rq_capped(r, c, _) == True{} : Bool}
  LP.qw.capped(QSpec.waves(List.length(&2, Nat, sizes), k), r, c, k, LP.qw.waves(k, List.length(&2, Nat, sizes), LP.qw.k_pos(w, Nat.sub(c, r), LN.rq.sub_pos(r, c, hr2))), LP.qw.k_room(w, Nat.sub(c, r)), LN.rq.lt_le(r, c, hr2))

def RlmQuery.rlm_query_cap_bound(r, c, w, b, u, sizes, ws, e):
  cb.go(r, c, w, sizes, ws, LP.qp.admitted(r, c, w, b, u, sizes, ws, e))
