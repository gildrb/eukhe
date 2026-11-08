# eukhe: the proof of LAW infer_threshold_plan_exact
# Part by part: the base (taking the sizes away one at a time is taking
# their sum, ipe.less), the budget (the target is the spec's,
# LAThreshold.gt.target), the cut (the forward walk is the spec's scan,
# LAWalk.iw.cut), the threshold (the hard window is the spec's test,
# ipe.past; the last turn's threshold is LAW infer_threshold_over_exact)
# and the gate (taking the kept sizes from the room left is comparing
# their sum, ipe.within).

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/nat.bend as LNat
import ./base.bend as LAThreshold
import ./base/walk.bend as LAWalk
import ./infer_threshold_over_exact.bend as PInferThresholdOverExact

# t less a, then less b, is t less a + b
def ipe.sub_sub(a: Nat, t: Nat, -b: Nat) -> {Nat.sub(Nat.sub(t, a), b) == Nat.sub(t, Nat.add(a, b)) : Nat}:
  match a t:
    case 0n 0n:
      {==}
    case 0n 1n+t1:
      {==}
    case 1n+a1 0n:
      {==}
    case 1n+a1 1n+t1:
      ipe.sub_sub(a1, t1, b)

# the base: t less every size, taken one at a time
def ipe.less(xs: List<&2, Nat>, +t: Nat) -> {M.less(xs, t) == Nat.sub(t, InferThreshold.sum(xs)) : Nat}:
  match xs:
    case Nil{}:
      match t:
        case 0n:
          {==}
        case 1n+t1:
          {==}
    case +x <> +rest:
      +s = InferThreshold.sum(rest)
      Equal.trans(Nat, M.less(rest, Nat.sub(t, x)), Nat.sub(Nat.sub(t, x), s), Nat.sub(t, Nat.add(s, x)),
        ipe.less(rest, Nat.sub(t, x)),
        Equal.trans(Nat, Nat.sub(Nat.sub(t, x), s), Nat.sub(t, Nat.add(x, s)), Nat.sub(t, Nat.add(s, x)),
          ipe.sub_sub(x, t, s), Equal.cong(Nat, Nat, z => Nat.sub(t, z), Nat.add(x, s), Nat.add(s, x), LNat.add_comm(x, s))))

# a + K is within n exactly when a is and K is within what a leaves of n
def ipe.le_add(a: Nat, n: Nat, -k: Nat) -> {Nat.is_le(Nat.add(a, k), n) == Bool.and(Nat.is_le(a, n), Nat.is_le(k, Nat.sub(n, a))) : Bool}:
  match a n:
    case 0n 0n:
      {==}
    case 0n 1n+n1:
      {==}
    case 1n+a1 0n:
      {==}
    case 1n+a1 1n+n1:
      ipe.le_add(a1, n1, k)

# the k newest sizes taken from room one at a time: their sum is within it
def ipe.within(xs: List<&2, Nat>, k: Nat, +room: Nat) -> {M.kept_within(xs, k, room) == Nat.is_le(InferThreshold.held(k, xs), room) : Bool}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          Equal.sym(Bool, Nat.is_le(0n, room), True{}, LNat.pq.le0(room))
        case 1n+j:
          Equal.sym(Bool, Nat.is_le(0n, room), True{}, LNat.pq.le0(room))
    case +x <> +rest:
      match k:
        case 0n:
          Equal.sym(Bool, Nat.is_le(0n, room), True{}, LNat.pq.le0(room))
        case 1n++j:
          +h = InferThreshold.held(j, rest)
          %Equal.sym(Bool, M.kept_within(rest, j, Nat.sub(room, x)), Nat.is_le(h, Nat.sub(room, x)), ipe.within(rest, j, Nat.sub(room, x))) : {Bool.and(Nat.is_le(x, room), _) == Nat.is_le(Nat.add(h, x), room) : Bool}
          %ipe.le_add(x, room, h) : {_ == Nat.is_le(Nat.add(h, x), room) : Bool}
          Equal.cong(Nat, Bool, z => Nat.is_le(z, room), Nat.add(x, h), Nat.add(h, x), LNat.add_comm(x, h))

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
      +a = Bool.and(Nat.is_le(base, tgt), M.kept_within(xs, k, Nat.sub(tgt, base)))
      +e = Equal.trans(Bool, a, Bool.and(Nat.is_le(base, tgt), Nat.is_le(InferThreshold.held(k, xs), Nat.sub(tgt, base))), Nat.is_le(Nat.add(base, InferThreshold.held(k, xs)), tgt),
        Equal.cong(Bool, Bool, z => Bool.and(Nat.is_le(base, tgt), z), M.kept_within(xs, k, Nat.sub(tgt, base)), Nat.is_le(InferThreshold.held(k, xs), Nat.sub(tgt, base)), ipe.within(xs, k, Nat.sub(tgt, base))),
        Equal.sym(Bool, Nat.is_le(Nat.add(base, InferThreshold.held(k, xs)), tgt), Bool.and(Nat.is_le(base, tgt), Nat.is_le(InferThreshold.held(k, xs), Nat.sub(tgt, base))), ipe.le_add(base, tgt, InferThreshold.held(k, xs))))
      %e : {M.over.early(a) == InferThreshold.reach_spec.at(_) : M.Over}
      ipe.early(a)

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

# The threshold after the turn
# ----------------------------

# a request is past the hard window: t > w, or t + r > w with a negative
# reserve
def ipe.past(+w: Nat, r: M.Z, +t: Nat) -> {Nat.is_le(M.hard_at(w, r), t) == InferThreshold.past_spec(t, r, w) : Bool}:
  match r:
    case M.Up{a}:
      Equal.sym(Bool, Nat.is_lt(w, t), Nat.is_le(1n+w, t), LAThreshold.gt.lt_le(w, t))
    case M.Down{+a}:
      Equal.sym(Bool, Nat.is_lt(1n+Nat.add(a, w), t), Nat.is_le(2n+Nat.add(a, w), t), LAThreshold.gt.lt_le(1n+Nat.add(a, w), t))

def ipe.due.at(p: Bool, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z) -> {M.due.at(p, last, w, r, m) == InferThreshold.due_spec.at(p, last, r, m, w) : M.Over}:
  match p:
    case True{}:
      {==}
    case False{}:
      InferThreshold.infer_threshold_over_exact(True{}, last, w, r, m)

# the threshold a request compacts at is the spec's
def ipe.due(on: Bool, +t: Nat, +last: Nat, w: Nat, +r: M.Z, +m: M.Z) -> {M.due(on, t, last, w, r, m) == InferThreshold.due_spec(on, t, last, w, r, m) : M.Over}:
  match on:
    case False{}:
      {==}
    case True{}:
      match w:
        case 0n:
          {==}
        case 1n++v:
          %ipe.past(1n+v, r, t) : {M.due.at(Nat.is_le(M.hard_at(1n+v, r), t), last, 1n+v, r, m) == InferThreshold.due_spec.at(_, last, r, m, 1n+v) : M.Over}
          ipe.due.at(Nat.is_le(M.hard_at(1n+v, r), t), last, 1n+v, r, m)

# The plan
# --------

def ipe.fin(+xs: List<&2, Nat>, +o: M.Over, -o2: M.Over, +c: Maybe<&2, Nat>, -c2: Maybe<&2, Nat>, +ba: Nat, -ba2: Nat, +tg: Nat, -tg2: Nat, eo: {o == o2 : M.Over}, ec: {c == c2 : Maybe<&2, Nat>}, eb: {ba == ba2 : Nat}, et: {tg == tg2 : Nat}) -> {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o2, c2, xs, ba2, tg2), c2} : M.Plan}:
  %eo : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(_, c2, xs, ba2, tg2), c2} : M.Plan}
  %ec : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, _, xs, ba2, tg2), _} : M.Plan}
  %eb : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, c, xs, _, tg2), c} : M.Plan}
  %et : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{InferThreshold.gate_spec(o, c, xs, ba, _), c} : M.Plan}
  %ipe.gate(o, c, xs, ba, tg) : {M.Plan{M.gate(o, c, xs, ba, tg), c} == M.Plan{_, c} : M.Plan}
  {==}

def ipe.plan(on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, eo: {M.due(on, t, last, w, r, m) == InferThreshold.due_spec(on, t, last, w, r, m) : M.Over}) -> {M.plan(on, t, last, w, r, m, keep, full, xs, cuts) == InferThreshold.plan_spec(on, t, last, w, r, m, keep, full, xs, cuts) : M.Plan}:
  +ba = M.less(xs, t)
  +ba2 = Nat.sub(t, InferThreshold.sum(xs))
  +eb = ipe.less(xs, t)
  ipe.fin(xs, M.due(on, t, last, w, r, m), InferThreshold.due_spec(on, t, last, w, r, m),
    M.cut(xs, cuts, M.budget(w, r, m, keep, ba), full), InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(w, r, m, keep, ba2), full),
    ba, ba2, M.target(w, r, m), InferThreshold.target_spec(w, r, m),
    eo, ipe.cut(xs, cuts, full, w, r, m, keep, ba, ba2, eb), eb, LAThreshold.gt.target(w, r, m))

def InferThreshold.infer_threshold_plan_exact(on, t, last, w, r, m, keep, full, xs, cuts):
  match on:
    case True{}:
      ipe.plan(True{}, t, last, w, r, m, keep, full, xs, cuts, ipe.due(True{}, t, last, w, r, m))
    case False{}:
      ipe.plan(False{}, t, last, w, r, m, keep, full, xs, cuts, ipe.due(False{}, t, last, w, r, m))
