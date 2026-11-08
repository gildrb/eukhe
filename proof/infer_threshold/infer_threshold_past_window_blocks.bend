# eukhe: the proof of LAW infer_threshold_past_window_blocks
# The plan is the spec's (LAW infer_threshold_plan_exact). A request past
# the hard window is due at the blocking threshold whatever its last turn
# reached, and the gate keeps it with the plan's cut.

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ./infer_threshold_plan_exact.bend as PInferThresholdPlanExact

def pwb.gate(-c: Maybe<&2, Nat>, -k: Nat, -xs: List<&2, Nat>, -base: Nat, -tgt: Nat, ec: {c == Some{k} : Maybe<&2, Nat>}) -> {InferThreshold.gate_spec(M.Blocks{}, c, xs, base, tgt) == M.Blocks{} : M.Over}:
  %Equal.sym(Maybe<&2, Nat>, c, Some{k}, ec) : {InferThreshold.gate_spec(M.Blocks{}, _, xs, base, tgt) == M.Blocks{} : M.Over}
  {==}

def pwb.over(-o: M.Over, -c: Maybe<&2, Nat>, -k: Nat, -xs: List<&2, Nat>, -base: Nat, -tgt: Nat, eo: {o == M.Blocks{} : M.Over}, ec: {c == Some{k} : Maybe<&2, Nat>}) -> {InferThreshold.gate_spec(o, c, xs, base, tgt) == M.Blocks{} : M.Over}:
  %Equal.sym(M.Over, o, M.Blocks{}, eo) : {InferThreshold.gate_spec(_, c, xs, base, tgt) == M.Blocks{} : M.Over}
  pwb.gate(c, k, xs, base, tgt, ec)

# past the window, the request blocks
def pwb.due(-t: Nat, -last: Nat, -v: Nat, -r: M.Z, -m: M.Z, past: {InferThreshold.past_spec(t, r, 1n+v) == True{} : Bool}) -> {InferThreshold.due_spec(True{}, t, last, 1n+v, r, m) == M.Blocks{} : M.Over}:
  %Equal.sym(Bool, InferThreshold.past_spec(t, r, 1n+v), True{}, past) : {InferThreshold.due_spec.at(_, last, r, m, 1n+v) == M.Blocks{} : M.Over}
  {==}

# the plan's cut is the spec's
def pwb.cut(-t: Nat, -last: Nat, -v: Nat, -r: M.Z, -m: M.Z, -keep: Nat, -full: Nat, -xs: List<&2, Nat>, -cuts: List<&2, Nat>, -k: Nat,
  pe: {M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts) == InferThreshold.plan_spec(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts) : M.Plan},
  cut: {M.Plan.cut(M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) == Some{k} : Maybe<&2, Nat>})
  -> {InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(1n+v, r, m, keep, Nat.sub(t, InferThreshold.sum(xs))), full) == Some{k} : Maybe<&2, Nat>}:
  %pe : {M.Plan.cut(_) == Some{k} : Maybe<&2, Nat>}
  cut

def InferThreshold.infer_threshold_past_window_blocks(t, last, v, r, m, keep, full, xs, cuts, k, past, cut):
  +pe = InferThreshold.infer_threshold_plan_exact(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)
  +ec = pwb.cut(t, last, v, r, m, keep, full, xs, cuts, k, pe, cut)
  %Equal.sym(M.Plan, M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts), InferThreshold.plan_spec(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts), pe) : {M.Plan.over(_) == M.Blocks{} : M.Over}
  pwb.over(InferThreshold.due_spec(True{}, t, last, 1n+v, r, m), InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(1n+v, r, m, keep, Nat.sub(t, InferThreshold.sum(xs))), full), k, xs, Nat.sub(t, InferThreshold.sum(xs)), InferThreshold.target_spec(1n+v, r, m),
    pwb.due(t, last, v, r, m, past), ec)
