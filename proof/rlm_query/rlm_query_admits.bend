# eukhe: the proof of LAW rlm_query_admits
#
# PROOF: the decision is the spec's (qp.plan); within the budget the budget test is false (qp.within) and below the cap the cap test is false, so the spec admits.

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def RlmQuery.rlm_query_admits(r, c, w, b, u, sizes, within, room):
  %Equal.sym(Rq.Plan, Rq.plan(r, c, w, b, u, sizes), QSpec.plan(r, c, w, b, u, sizes), LP.qp.plan(r, c, w, b, u, sizes)) : {RlmQuery.rq_admitted(_) == True{} : Bool}
  %Equal.sym(Bool, QSpec.over_budget(b, u, QSpec.total(sizes)), False{}, LP.qp.within(b, u, QSpec.total(sizes), within)) : {RlmQuery.rq_admitted(QSpec.plan.of(_, r, c, w, b, u, sizes)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(c, r), False{}, LN.rq.lt_not_le(r, c, room)) : {RlmQuery.rq_admitted(QSpec.plan.cap(_, c, r, w, List.length(&2, Nat, sizes))) == True{} : Bool}
  {==}
