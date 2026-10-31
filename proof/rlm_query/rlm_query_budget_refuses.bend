# eukhe: the proof of LAW rlm_query_budget_refuses
#
# PROOF: the decision is the spec's (qp.plan); a set budget passed makes the spec's budget test true, so the spec refuses for the budget.

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def RlmQuery.rlm_query_budget_refuses(r, c, w, b, u, sizes, set, over):
  %Equal.sym(Rq.Plan, Rq.plan(r, c, w, b, u, sizes), QSpec.plan(r, c, w, b, u, sizes), LP.qp.plan(r, c, w, b, u, sizes)) : {_ == Rq.Refused{Rq.OverBudget{QSpec.total(sizes), Nat.sub(b, u), b}} : Rq.Plan}
  %Equal.sym(Bool, Nat.is_lt(0n, b), True{}, set) : {QSpec.plan.of(Bool.and(_, Nat.is_lt(b, Nat.add(u, QSpec.total(sizes)))), r, c, w, b, u, sizes) == Rq.Refused{Rq.OverBudget{QSpec.total(sizes), Nat.sub(b, u), b}} : Rq.Plan}
  %Equal.sym(Bool, Nat.is_lt(b, Nat.add(u, QSpec.total(sizes))), True{}, over) : {QSpec.plan.of(Bool.and(True{}, _), r, c, w, b, u, sizes) == Rq.Refused{Rq.OverBudget{QSpec.total(sizes), Nat.sub(b, u), b}} : Rq.Plan}
  {==}
