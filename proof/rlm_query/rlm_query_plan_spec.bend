# eukhe: the proof of LAW rlm_query_plan_spec
#
# PROOF: the code's total, budget test (by what is left of the budget: qp.past, rq.lt_or), wave width and waves are the spec's (qp.total, qp.over, qp.width; the waves follow Nat.divmod's loop, qp.go).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/nat.bend as LN
import ./base/plan.bend as LP


def RlmQuery.rlm_query_plan_spec(r, c, w, b, u, sizes):
  LP.qp.plan(r, c, w, b, u, sizes)
