# eukhe: the proof of LAW infer_threshold_plan_exact
# Part by part: the base (total is sum), the budget (the target is the
# spec's, LAThreshold.gt.target), the cut (the forward walk is the spec's
# scan, LAWalk.iw.cut), the threshold (LAW infer_threshold_over_exact) and
# the gate (kept is held).

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/nat.bend as LNat
import ./base.bend as LAThreshold
import ./base/walk.bend as LAWalk
import ./infer_threshold_over_exact.bend as PInferThresholdOverExact

def ipe.total(xs: List<&2, Nat>) -> {M.total(xs) == InferThreshold.sum(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ipe.total(rest) : {Nat.add(x, M.total(rest)) == Nat.add(_, x) : Nat}
      LNat.add_comm(x, M.total(rest))

def ipe.kept(xs: List<&2, Nat>, k: Nat) -> {M.kept(xs, k) == InferThreshold.held(k, xs) : Nat}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case +x <> +rest:
      match k:
        case 0n:
          {==}
        case 1n++j:
          %ipe.kept(rest, j) : {Nat.add(x, M.kept(rest, j)) == Nat.add(_, x) : Nat}
          LNat.add_comm(x, M.kept(rest, j))

# The budget
# ----------

def ipe.least(le: Bool, a: Nat, b: Nat) -> {M.least(a, b, le) == InferThreshold.budget_spec.min(le, a, b) : Nat}:
  match le:
    case True{}:
      {==}
    case False{}:
      {==}

def ipe.budget(w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +base: Nat) -> {M.budget(w, r, m, keep, base) == InferThreshold.budget_spec(w, r, m, keep, base) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n++v:
      %LAThreshold.gt.target(1n+v, r, m) : {M.least(keep, Nat.sub(M.target(1n+v, r, m), base), Nat.is_le(keep, Nat.sub(M.target(1n+v, r, m), base))) == InferThreshold.budget_spec.min(Nat.is_le(keep, Nat.sub(_, base)), keep, Nat.sub(_, base)) : Nat}
      ipe.least(Nat.is_le(keep, Nat.sub(M.target(1n+v, r, m), base)), keep, Nat.sub(M.target(1n+v, r, m), base))

# the cut within the model's budget is the spec's within the spec's
def ipe.cut(+xs: List<&2, Nat>, +cuts: List<&2, Nat>, +full: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +ba: Nat, -bs: Nat, eb: {ba == bs : Nat}) -> {M.cut(xs, cuts, M.budget(w, r, m, keep, ba), full) == InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(w, r, m, keep, bs), full) : Maybe<&2, Nat>}:
  %eb : {M.cut(xs, cuts, M.budget(w, r, m, keep, ba), full) == InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(w, r, m, keep, _), full) : Maybe<&2, Nat>}
  %ipe.budget(w, r, m, keep, ba) : {M.cut(xs, cuts, M.budget(w, r, m, keep, ba), full) == InferThreshold.cut_spec(xs, cuts, _, full) : Maybe<&2, Nat>}
  LAWalk.iw.cut(xs, cuts, M.budget(w, r, m, keep, ba), full)

# The gate
# --------

def ipe.early(b: Bool) -> {M.over.early(b) == InferThreshold.reach_spec.at(b) : M.Over}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ipe.reach(c: Maybe<&2, Nat>, +xs: List<&2, Nat>, +base: Nat, +tgt: Nat) -> {M.early.reach(c, xs, base, tgt) == InferThreshold.reach_spec(c, xs, base, tgt) : M.Over}:
  match c:
    case None{}:
      {==}
    case Some{+k}:
      %ipe.kept(xs, k) : {M.over.early(Nat.is_le(Nat.add(base, M.kept(xs, k)), tgt)) == InferThreshold.reach_spec.at(Nat.is_le(Nat.add(base, _), tgt)) : M.Over}
      ipe.early(Nat.is_le(Nat.add(base, M.kept(xs, k)), tgt))

def ipe.gate(o: M.Over, c: Maybe<&2, Nat>, +xs: List<&2, Nat>, +base: Nat, +tgt: Nat) -> {M.gate(o, c, xs, base, tgt) == InferThreshold.gate_spec(o, c, xs, base, tgt) : M.Over}:
  match o:
    case M.Under{}:
      {==}
    case M.Early{}:
      ipe.reach(c, xs, base, tgt)
    case M.Blocks{}:
      match c:
        case None{}:
          {==}
        case Some{k}:
          {==}

# The plan
# --------

def ipe.fin(+xs: List<&2, Nat>, +o: M.Over, -o2: M.Over, +c: Maybe<&2, Nat>, -c2: Maybe<&2, Nat>, +ba: Nat, -ba2: Nat, +tg: Nat, -tg2: Nat, eo: {o == o2 : M.Over}, ec: {c == c2 : Maybe<&2, Nat>}, eb: {ba == ba2 : Nat}, et: {tg == tg2 : Nat}) -> {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o2, c2, xs, ba2, tg2), c2} : M.Plan}:
  %eo : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(_, c2, xs, ba2, tg2), c2} : M.Plan}
  %ec : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, _, xs, ba2, tg2), _} : M.Plan}
  %eb : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, c, xs, _, tg2), c} : M.Plan}
  %et : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, c, xs, ba, _), c} : M.Plan}
  %ipe.gate(o, c, xs, ba, tg) : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{_, c} : M.Plan}
  {==}

def ipe.plan(on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, eo: {M.over(on, t, w, r, m) == InferThreshold.over_spec(on, t, w, r, m) : M.Over}) -> {M.plan(on, t, w, r, m, keep, full, xs, cuts) == InferThreshold.plan_spec(on, t, w, r, m, keep, full, xs, cuts) : M.Plan}:
  +ba = Nat.sub(t, M.total(xs))
  +ba2 = Nat.sub(t, InferThreshold.sum(xs))
  +eb = Equal.cong(Nat, Nat, s => Nat.sub(t, s), M.total(xs), InferThreshold.sum(xs), ipe.total(xs))
  ipe.fin(xs, M.over(on, t, w, r, m), InferThreshold.over_spec(on, t, w, r, m),
    M.cut(xs, cuts, M.budget(w, r, m, keep, ba), full), InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(w, r, m, keep, ba2), full),
    ba, ba2, M.target(w, r, m), InferThreshold.target_spec(w, r, m),
    eo, ipe.cut(xs, cuts, full, w, r, m, keep, ba, ba2, eb), eb, LAThreshold.gt.target(w, r, m))

def InferThreshold.infer_threshold_plan_exact(on, t, w, r, m, keep, full, xs, cuts):
  match on:
    case True{}:
      ipe.plan(True{}, t, w, r, m, keep, full, xs, cuts, InferThreshold.infer_threshold_over_exact(True{}, t, w, r, m))
    case False{}:
      ipe.plan(False{}, t, w, r, m, keep, full, xs, cuts, InferThreshold.infer_threshold_over_exact(False{}, t, w, r, m))
