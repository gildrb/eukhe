# eukhe: the proof of LAW infer_threshold_turn_under
# The plan is the spec's (LAW infer_threshold_plan_exact). A request
# within the hard window reads the threshold of its last turn alone, which
# is under every one, and the gate passes Under.

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ./infer_threshold_plan_exact.bend as PInferThresholdPlanExact

def ttu.gate(-o: M.Over, -c: Maybe<&2, Nat>, -xs: List<&2, Nat>, -base: Nat, -tgt: Nat, eo: {o == M.Under{} : M.Over}) -> {InferThreshold.gate_spec(o, c, xs, base, tgt) == M.Under{} : M.Over}:
  %Equal.sym(M.Over, o, M.Under{}, eo) : {InferThreshold.gate_spec(_, c, xs, base, tgt) == M.Under{} : M.Over}
  {==}

# within the window, the threshold is the last turn's
def ttu.due(-t: Nat, +last: Nat, +v: Nat, +r: M.Z, +m: M.Z, within: {InferThreshold.past_spec(t, r, 1n+v) == False{} : Bool}, under: {InferThreshold.over_spec(True{}, last, 1n+v, r, m) == M.Under{} : M.Over}) -> {InferThreshold.due_spec(True{}, t, last, 1n+v, r, m) == M.Under{} : M.Over}:
  %Equal.sym(Bool, InferThreshold.past_spec(t, r, 1n+v), False{}, within) : {InferThreshold.due_spec.at(_, last, r, m, 1n+v) == M.Under{} : M.Over}
  under

def InferThreshold.infer_threshold_turn_under(t, last, v, r, m, keep, full, xs, cuts, within, under):
  %Equal.sym(M.Plan, M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts), InferThreshold.plan_spec(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts), InferThreshold.infer_threshold_plan_exact(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) : {M.Plan.over(_) == M.Under{} : M.Over}
  ttu.gate(InferThreshold.due_spec(True{}, t, last, 1n+v, r, m), InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(1n+v, r, m, keep, Nat.sub(t, InferThreshold.sum(xs))), full), xs, Nat.sub(t, InferThreshold.sum(xs)), InferThreshold.target_spec(1n+v, r, m),
    ttu.due(t, last, v, r, m, within, under))
