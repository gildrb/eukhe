# eukhe: the proof of LAW rlm_query_full_refuses
#
# PROOF: the decision is the spec's (qp.plan); within the budget the spec's budget test is false (qp.within), so a full cap refuses.

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def RlmQuery.rlm_query_full_refuses(r, c, w, b, u, sizes, within, full):
  %Equal.sym(Rq.Plan, Rq.plan(r, c, w, b, u, sizes), QSpec.plan(r, c, w, b, u, sizes), LP.qp.plan(r, c, w, b, u, sizes)) : {_ == Rq.Refused{Rq.Full{c}} : Rq.Plan}
  %Equal.sym(Bool, QSpec.over_budget(b, u, QSpec.total(sizes)), False{}, LP.qp.within(b, u, QSpec.total(sizes), within)) : {QSpec.plan.of(_, r, c, w, b, u, sizes) == Rq.Refused{Rq.Full{c}} : Rq.Plan}
  %Equal.sym(Bool, Nat.is_le(c, r), True{}, full) : {QSpec.plan.cap(_, c, r, w, List.length(&2, Nat, sizes)) == Rq.Refused{Rq.Full{c}} : Rq.Plan}
  {==}
