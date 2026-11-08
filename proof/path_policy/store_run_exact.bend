# eukhe: the proof of LAW store_run_exact
#
# PROOF: by induction on the writes (ps.run). One write (ps.step): the
# model's resolution is pp_real (path_real_exact); on a real path Res{at, l}
# (ps.step_at) the model's class is pp_class (path_judge_class_exact: the
# judgment's class is class_res), the gate's verdict on a write of it is
# the spec's (gate_runs_exact, whose effects of a write are pp_write_effs),
# and the model's write at `at` is pp_set (ps.set: by induction on the
# cells, Tl.ids.eq being pp_same).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./base.bend as LA
import ./path_real_exact.bend as PPathRealExact
import ./path_judge_class_exact.bend as PPathJudgeClassExact
import ./gate_runs_exact.bend as PGateRunsExact

def ps.set_pick(hit: Bool, +at: List<&2, Nat>, +v: Nat, c: Pp.Cell, rest: List<&2, Pp.Cell>, later: List<&2, Pp.Cell>) -> {Pp.set.pick(hit, c, at, v, rest, later) == PathPolicyGate.pp_set_pick(hit, at, v, c, rest, later) : List<&2, Pp.Cell>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.set(cs: List<&2, Pp.Cell>, +at: List<&2, Nat>, +v: Nat) -> {Pp.set(cs, at, v) == PathPolicyGate.pp_set(cs, at, v) : List<&2, Pp.Cell>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case Pp.Cell{+a, +w}:
          %LA.pp.ids_same(a, at) : {Pp.set(Pp.Cell{a, w} <> rest, at, v) == PathPolicyGate.pp_set_pick(_, at, v, Pp.Cell{a, w}, rest, PathPolicyGate.pp_set(rest, at, v)) : List<&2, Pp.Cell>}
          %ps.set(rest, at, v) : {Pp.set(Pp.Cell{a, w} <> rest, at, v) == PathPolicyGate.pp_set_pick(Tl.ids.eq(a, at), at, v, Pp.Cell{a, w}, rest, _) : List<&2, Pp.Cell>}
          ps.set_pick(Tl.ids.eq(a, at), at, v, Pp.Cell{a, w}, rest, Pp.set(rest, at, v))

def ps.land(go: Bool, cs: List<&2, Pp.Cell>, +at: List<&2, Nat>, +v: Nat) -> {Pp.put.pick(go, cs, at, v) == PathPolicyGate.pp_land(go, cs, at, v) : List<&2, Pp.Cell>}:
  match go:
    case True{}:
      ps.set(cs, at, v)
    case False{}:
      {==}

def ps.step_at(r: Pp.Res, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, +v: Nat, +ans: Pp.Ans) -> {Pp.put.pick(Pp.runs(Pp.class_res(Pp.Pol{ro, ru, se}, r), Pp.Wr{}, auto, ans), cs, Pp.Res.at(r), v) == PathPolicyGate.pp_step_at(r, ro, ru, se, auto, cs, v, ans) : List<&2, Pp.Cell>}:
  match r:
    case Pp.Res{+at, +l}:
      %PathPolicy.path_judge_class_exact(ro, ru, se, at, l) : {Pp.put.pick(Pp.runs(Pp.class_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), Pp.Wr{}, auto, ans), cs, at, v) == PathPolicyGate.pp_land(Bool.or(PathPolicyGate.pp_auto_holds(auto, PathPolicyGate.pp_write_effs(_)), PathPolicyGate.pp_yes(ans)), cs, at, v) : List<&2, Pp.Cell>}
      %PathPolicyGate.gate_runs_exact(Pp.class_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), Pp.Wr{}, auto, ans) : {Pp.put.pick(Pp.runs(Pp.class_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), Pp.Wr{}, auto, ans), cs, at, v) == PathPolicyGate.pp_land(_, cs, at, v) : List<&2, Pp.Cell>}
      ps.land(Pp.runs(Pp.class_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), Pp.Wr{}, auto, ans), cs, at, v)

def ps.step(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, e: Pp.Put) -> {Pp.step(Pp.Pol{ro, ru, se}, ls, auto, cs, e) == PathPolicyGate.pp_step(ro, ru, se, ls, auto, cs, e) : List<&2, Pp.Cell>}:
  match e:
    case Pp.Put{+segs, +v, +ans}:
      %PathPolicy.path_real_exact(ls, segs) : {Pp.step(Pp.Pol{ro, ru, se}, ls, auto, cs, Pp.Put{segs, v, ans}) == PathPolicyGate.pp_step_at(_, ro, ru, se, auto, cs, v, ans) : List<&2, Pp.Cell>}
      ps.step_at(Pp.real(ls, segs), ro, ru, se, auto, cs, v, ans)

def ps.run(es: List<&2, Pp.Put>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +cs: List<&2, Pp.Cell>) -> {Pp.run(es, Pp.Pol{ro, ru, se}, ls, auto, cs) == PathPolicyGate.pp_run(es, ro, ru, se, ls, auto, cs) : List<&2, Pp.Cell>}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %ps.step(ro, ru, se, ls, auto, cs, e) : {Pp.run(e <> rest, Pp.Pol{ro, ru, se}, ls, auto, cs) == PathPolicyGate.pp_run(rest, ro, ru, se, ls, auto, _) : List<&2, Pp.Cell>}
      ps.run(rest, ro, ru, se, ls, auto, Pp.step(Pp.Pol{ro, ru, se}, ls, auto, cs, e))

def PathPolicyGate.store_run_exact(es, ro, ru, se, ls, auto, cs):
  ps.run(es, ro, ru, se, ls, auto, cs)
