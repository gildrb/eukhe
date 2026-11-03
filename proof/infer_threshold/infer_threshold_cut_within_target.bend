# eukhe: the proof of LAW infer_threshold_cut_within_target
# The model's cut is the spec's (LAW infer_threshold_plan_exact). A cut
# the scan down finds holds at most the budget (icw.fs): at most keep and
# at most target - base, so base + kept is within the target when the base
# is; any other cut is the newest one.

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/nat.bend as LNat
import ./base/walk.bend as LAWalk
import ./infer_threshold_plan_exact.bend as PInferThresholdPlanExact

# A cut the scan down finds is within the budget
# ----------------------------------------------

def icw.ok(c: Maybe<&2, Nat>, xs: List<&2, Nat>, b: Nat) -> Bool:
  match c:
    case None{}:
      True{}
    case Some{j}:
      Nat.is_le(InferThreshold.held(j, xs), b)

def icw.fs.at(g: Bool, +p: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, eg: {Bool.and(InferThreshold.is_cut(cuts, n, 1n+p), Nat.is_le(InferThreshold.held(1n+p, xs), b)) == g : Bool}, ih: {icw.ok(InferThreshold.fit_spec(xs, cuts, n, b, p), xs, b) == True{} : Bool}) -> {icw.ok(InferThreshold.fit_spec.at(g, 1n+p, InferThreshold.fit_spec(xs, cuts, n, b, p)), xs, b) == True{} : Bool}:
  match g:
    case True{}:
      LAWalk.iw.and_r(InferThreshold.is_cut(cuts, n, 1n+p), Nat.is_le(InferThreshold.held(1n+p, xs), b), eg)
    case False{}:
      ih

def icw.fs(i: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat) -> {icw.ok(InferThreshold.fit_spec(xs, cuts, n, b, i), xs, b) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n++p:
      icw.fs.at(Bool.and(InferThreshold.is_cut(cuts, n, 1n+p), Nat.is_le(InferThreshold.held(1n+p, xs), b)), p, xs, cuts, n, b, {==}, icw.fs(p, xs, cuts, n, b))

# The budget's parts
# ------------------

def icw.room(le: Bool, +keep: Nat, +room: Nat, +h: Nat, el: {Nat.is_le(keep, room) == le : Bool}, hb: {Nat.is_le(h, InferThreshold.budget_spec.min(le, keep, room)) == True{} : Bool}) -> {Nat.is_le(h, room) == True{} : Bool}:
  match le:
    case True{}:
      LNat.pu.le_trans(h, keep, room, hb, el)
    case False{}:
      hb

def icw.keep(le: Bool, +keep: Nat, +room: Nat, +h: Nat, el: {Nat.is_le(keep, room) == le : Bool}, hb: {Nat.is_le(h, InferThreshold.budget_spec.min(le, keep, room)) == True{} : Bool}) -> {Nat.is_le(h, keep) == True{} : Bool}:
  match le:
    case True{}:
      hb
    case False{}:
      LNat.pu.le_trans(h, room, keep, hb, LAWalk.iw.nle(keep, room, el))

# base + h within the target when h is within target - base
def icw.sum(+base: Nat, +tgt: Nat, +h: Nat, hr: {Nat.is_le(h, Nat.sub(tgt, base)) == True{} : Bool}, bt: {Nat.is_le(base, tgt) == True{} : Bool}) -> {Nat.is_le(Nat.add(base, h), tgt) == True{} : Bool}:
  %LNat.pu.sub_add(base, tgt, bt) : {Nat.is_le(Nat.add(base, h), _) == True{} : Bool}
  LNat.ps.le_mono(base, h, Nat.sub(tgt, base), hr)

def icw.tomin(+h: Nat, -b: Nat, -mn: Nat, eB: {b == mn : Nat}, hb: {Nat.is_le(h, b) == True{} : Bool}) -> {Nat.is_le(h, mn) == True{} : Bool}:
  %eB : {Nat.is_le(h, _) == True{} : Bool}
  hb

# a cut within the budget is within the target and keep
def icw.fits(+j: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +base: Nat, +tgt: Nat, +keep: Nat, +hb: {Nat.is_le(InferThreshold.held(j, xs), InferThreshold.budget_spec.min(Nat.is_le(keep, Nat.sub(tgt, base)), keep, Nat.sub(tgt, base))) == True{} : Bool}, bt: {Nat.is_le(base, tgt) == True{} : Bool}) -> {InferThreshold.within(j, xs, cuts, base, tgt, keep) == True{} : Bool}:
  +h = InferThreshold.held(j, xs)
  +room = Nat.sub(tgt, base)
  +le = Nat.is_le(keep, room)
  +hr = icw.room(le, keep, room, h, {==}, hb)
  +hk = icw.keep(le, keep, room, h, {==}, hb)
  %Equal.sym(Bool, Nat.is_le(Nat.add(base, h), tgt), True{}, icw.sum(base, tgt, h, hr, bt)) : {Bool.or(Bool.and(_, Nat.is_le(h, keep)), InferThreshold.is_newest(InferThreshold.newest_spec(xs, cuts), j)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(h, keep), True{}, hk) : {Bool.or(Bool.and(True{}, _), InferThreshold.is_newest(InferThreshold.newest_spec(xs, cuts), j)) == True{} : Bool}
  {==}

# The cut
# -------

def icw.val(c: Maybe<&2, Nat>) -> Nat:
  match c:
    case None{}:
      0n
    case Some{j}:
      j

def icw.left.at(lt: Bool, +j: Nat, -k: Nat, e: {InferThreshold.fit_spec.at(lt, j, None{}) == Some{k} : Maybe<&2, Nat>}) -> {Some{j} == Some{k} : Maybe<&2, Nat>}:
  match lt:
    case True{}:
      e
    case False{}:
      LAWalk.iw.ns({Some{j} == Some{k} : Maybe<&2, Nat>}, k, e)

def icw.left(c: Maybe<&2, Nat>, +full: Nat, -k: Nat, e: {InferThreshold.left_spec(c, full) == Some{k} : Maybe<&2, Nat>}) -> {c == Some{k} : Maybe<&2, Nat>}:
  match c:
    case None{}:
      e
    case Some{+j}:
      icw.left.at(Nat.is_lt(j, full), j, k, e)

# a cut the scan down finds holds at most b
def icw.got(+j: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +b: Nat, eF: {InferThreshold.fit_spec(xs, cuts, List.length(&2, Nat, xs), b, List.length(&2, Nat, xs)) == Some{j} : Maybe<&2, Nat>}) -> {Nat.is_le(InferThreshold.held(j, xs), b) == True{} : Bool}:
  %eF : {icw.ok(_, xs, b) == True{} : Bool}
  icw.fs(List.length(&2, Nat, xs), xs, cuts, List.length(&2, Nat, xs), b)

def icw.or(f: Maybe<&2, Nat>, +k: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +base: Nat, +tgt: Nat, +keep: Nat, +b: Nat,
  eF: {InferThreshold.fit_spec(xs, cuts, List.length(&2, Nat, xs), b, List.length(&2, Nat, xs)) == f : Maybe<&2, Nat>},
  e: {InferThreshold.or_else(f, InferThreshold.newest_spec(xs, cuts)) == Some{k} : Maybe<&2, Nat>},
  bt: {Nat.is_le(base, tgt) == True{} : Bool},
  eB: {b == InferThreshold.budget_spec.min(Nat.is_le(keep, Nat.sub(tgt, base)), keep, Nat.sub(tgt, base)) : Nat})
  -> {InferThreshold.within(k, xs, cuts, base, tgt, keep) == True{} : Bool}:
  match f:
    case None{}:
      %Equal.sym(Maybe<&2, Nat>, InferThreshold.newest_spec(xs, cuts), Some{k}, e) : {Bool.or(InferThreshold.fits_spec(k, xs, base, tgt, keep), InferThreshold.is_newest(_, k)) == True{} : Bool}
      %LNat.pf.nat_eq_refl(k) : {Bool.or(InferThreshold.fits_spec(k, xs, base, tgt, keep), _) == True{} : Bool}
      LAWalk.iw.or_t(InferThreshold.fits_spec(k, xs, base, tgt, keep))
    case Some{+j}:
      +jk = Equal.cong(Maybe<&2, Nat>, Nat, icw.val, Some{j}, Some{k}, e)
      +hb = icw.tomin(InferThreshold.held(j, xs), b, InferThreshold.budget_spec.min(Nat.is_le(keep, Nat.sub(tgt, base)), keep, Nat.sub(tgt, base)), eB, icw.got(j, xs, cuts, b, eF))
      %jk : {InferThreshold.within(_, xs, cuts, base, tgt, keep) == True{} : Bool}
      icw.fits(j, xs, cuts, base, tgt, keep, hb, bt)

# the plan's cut is the spec's
def icw.cs(-on: Bool, +t: Nat, +last: Nat, +v: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, -k: Nat,
  pe: {M.plan(on, t, last, 1n+v, r, m, keep, full, xs, cuts) == InferThreshold.plan_spec(on, t, last, 1n+v, r, m, keep, full, xs, cuts) : M.Plan},
  cut: {M.Plan.cut(M.plan(on, t, last, 1n+v, r, m, keep, full, xs, cuts)) == Some{k} : Maybe<&2, Nat>})
  -> {InferThreshold.cut_spec(xs, cuts, InferThreshold.budget_spec(1n+v, r, m, keep, Nat.sub(t, InferThreshold.sum(xs))), full) == Some{k} : Maybe<&2, Nat>}:
  %pe : {M.Plan.cut(_) == Some{k} : Maybe<&2, Nat>}
  cut

def icw.law(-on: Bool, +t: Nat, +last: Nat, +v: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +k: Nat,
  room: {Nat.is_le(Nat.sub(t, InferThreshold.sum(xs)), InferThreshold.target_spec(1n+v, r, m)) == True{} : Bool},
  cut: {M.Plan.cut(M.plan(on, t, last, 1n+v, r, m, keep, full, xs, cuts)) == Some{k} : Maybe<&2, Nat>},
  pe: {M.plan(on, t, last, 1n+v, r, m, keep, full, xs, cuts) == InferThreshold.plan_spec(on, t, last, 1n+v, r, m, keep, full, xs, cuts) : M.Plan})
  -> {InferThreshold.within(k, xs, cuts, Nat.sub(t, InferThreshold.sum(xs)), InferThreshold.target_spec(1n+v, r, m), keep) == True{} : Bool}:
  +base = Nat.sub(t, InferThreshold.sum(xs))
  +b = InferThreshold.budget_spec(1n+v, r, m, keep, base)
  +n = List.length(&2, Nat, xs)
  +cs = icw.cs(on, t, last, v, r, m, keep, full, xs, cuts, k, pe, cut)
  +oc = icw.left(InferThreshold.or_else(InferThreshold.fit_spec(xs, cuts, n, b, n), InferThreshold.newest_spec(xs, cuts)), full, k, cs)
  icw.or(InferThreshold.fit_spec(xs, cuts, n, b, n), k, xs, cuts, base, InferThreshold.target_spec(1n+v, r, m), keep, b, {==}, oc, room, {==})

def InferThreshold.infer_threshold_cut_within_target(on, t, last, v, r, m, keep, full, xs, cuts, k, room, cut):
  match on:
    case True{}:
      icw.law(True{}, t, last, v, r, m, keep, full, xs, cuts, k, room, cut, InferThreshold.infer_threshold_plan_exact(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts))
    case False{}:
      icw.law(False{}, t, last, v, r, m, keep, full, xs, cuts, k, room, cut, InferThreshold.infer_threshold_plan_exact(False{}, t, last, 1n+v, r, m, keep, full, xs, cuts))
