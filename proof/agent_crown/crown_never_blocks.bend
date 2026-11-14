# eukhe: the proof of LAW crown_never_blocks
#
# PROOF: a tree event is taken exactly when the tree's step on the view is
# (the code's bounds and view are the spec's). A taken finish at p leaves a
# node at p that does not run (the edit puts the Finished node back at p);
# the charges taken off keep its status (base/view.bend ac_view.runs_shift),
# so the sweep cancels every running help leaf at p.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ../agent_tree/base/edit.bend as E
import ../agent_tree/base/reach.bend as AR
import ./base/view.bend as V
import ./base/step.bend as St

def ac_fin.took_on(+s: T.Step, -hs: List<&2, A.Help>, -e: T.Ev) -> {AgentCrown.ctook(A.on_tree(s, hs, e)) == AgentCrown.took(s) : Bool}:
  match s:
    case T.Took{x}:
      {==}
    case T.Refused{why}:
      {==}

# a taken step leaves a node at p that does not run
def ac_fin.Stops(s: T.Step, +p: List<&2, T.Dir>) -> Type:
  match s:
    case T.Took{x}:
      {A.runs(A.node_at(p, x)) == False{} : Bool}
    case T.Refused{why}:
      Unit

# a taken local step leaves a node that does not run
def ac_fin.Done(s: T.Step) -> Type:
  match s:
    case T.Took{m}:
      {A.runs(Some{m}) == False{} : Bool}
    case T.Refused{why}:
      Unit

def ac_fin.settled_split(ok: Bool, +i: T.Info, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: List<&2, Maybe<&2, Nat>>) -> ac_fin.Done(T.finish_settled(ok, i, own, l, r, q)):
  match ok:
    case True{}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          {==}
    case False{}:
      Unit{}

def ac_fin.local_fin(+n: T.Node, +q: List<&2, Maybe<&2, Nat>>, +k: Nat) -> ac_fin.Done(T.local(T.OpFinish{q}, n, k)):
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              ac_fin.settled_split(Bool.and(Bool.not(T.running(T.st_of(T.info(l)))), Bool.not(T.running(T.st_of(T.info(r))))), T.Info{T.Running{}, s, lim, sp, dl, pa}, own, l, r, q)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_fin.lift_stops(+s: T.Step, +p: List<&2, T.Dir>, +t: T.Node, -n: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, d: ac_fin.Done(s)) -> ac_fin.Stops(E.at_edit.lift(s, p, t), p):
  match s:
    case T.Took{+m}:
      %Equal.sym(Maybe<&2, T.Node>, A.node_at(p, S.put(p, t, m)), S.node_at(p, S.put(p, t, m)), V.ac_view.node_at_eq(p, S.put(p, t, m))) : {A.runs(_) == False{} : Bool}
      %E.at_edit.node_at_put(p, t, n, m, e) : {A.runs(_) == False{} : Bool}
      d
    case T.Refused{why}:
      Unit{}

def ac_fin.via_stops(+m: Maybe<&2, T.Node>, +p: List<&2, T.Dir>, +t: T.Node, +q: List<&2, Maybe<&2, Nat>>, +k: Nat, e: {S.node_at(p, t) == m : Maybe<&2, T.Node>}) -> ac_fin.Stops(E.at_edit.via(m, p, t, T.OpFinish{q}, k), p):
  match m:
    case None{}:
      Unit{}
    case Some{+n}:
      ac_fin.lift_stops(T.local(T.OpFinish{q}, n, E.at_edit.npred(p, k)), p, t, n, e, ac_fin.local_fin(n, q, E.at_edit.npred(p, k)))

# a taken finish at p leaves a node at p that does not run
def ac_fin.step_stops(+b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, +q: List<&2, Maybe<&2, Nat>>) -> ac_fin.Stops(T.step(b, t, T.EvFinish{p, q}), p):
  %E.at_edit.edit_at(p, t, T.OpFinish{q}, T.bound_depth(b)) : ac_fin.Stops(_, p)
  ac_fin.via_stops(S.node_at(p, t), p, t, q, T.bound_depth(b), {==})

def ac_fin.cancel_quiet(st: T.Status) -> {Bool.or(False{}, Bool.not(T.running(T.cancel_st(st)))) == True{} : Bool}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

# one help leaf at q2 after the sweep: not at p, or not running
def ac_fin.one(c: Bool, +q2: List<&2, T.Dir>, +p: List<&2, T.Dir>, +y: T.Node, +st: T.Status, +dl: T.Lim, +e: T.Ev, ec: {CS.path_is(q2, p) == c : Bool}, h: {A.runs(A.node_at(p, y)) == False{} : Bool}) -> {Bool.or(Bool.not(c), Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(A.runs(A.node_at(q2, y))), A.help_late(dl, e)), st)))) == True{} : Bool}:
  match c:
    case True{}:
      +epq = V.ac_view.path_eq(q2, p, ec)
      +h2 = AR.at_reach.tr(List<&2, T.Dir>, p, q2, z => {A.runs(A.node_at(z, y)) == False{} : Bool}, Equal.sym(List<&2, T.Dir>, q2, p, epq), h)
      %Equal.sym(Bool, A.runs(A.node_at(q2, y)), False{}, h2) : {Bool.or(Bool.not(True{}), Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(_), A.help_late(dl, e)), st)))) == True{} : Bool}
      ac_fin.cancel_quiet(st)
    case False{}:
      {==}

# no node at p runs in y: the sweep leaves no help leaf at p running
def ac_fin.sweep_quiet(hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +y: T.Node, +e: T.Ev, +h: {A.runs(A.node_at(p, y)) == False{} : Bool}) -> {CS.none_run_at(p, A.sweep(hs, y, e)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case A.Help{+q2, +st, lim, sp, +dl}:
          AR.at_reach.and_t(Bool.or(Bool.not(CS.path_is(q2, p)), Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(A.runs(A.node_at(q2, y))), A.help_late(dl, e)), st)))), CS.none_run_at(p, A.sweep(rest, y, e)), ac_fin.one(CS.path_is(q2, p), q2, p, y, st, dl, e, {==}, h), ac_fin.sweep_quiet(rest, p, y, e, h))

def ac_fin.quiet_on(+s: T.Step, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +e: T.Ev, d: ac_fin.Stops(s, p)) -> {AgentCrown.help_quiet_at(p, A.on_tree(s, hs, e)) == True{} : Bool}:
  match s:
    case T.Took{x}:
      +h = Equal.trans(Bool, A.runs(A.node_at(p, A.shift(x, A.loads(hs), False{}))), A.runs(A.node_at(p, x)), False{}, V.ac_view.runs_shift(p, x, A.loads(hs), False{}), d)
      ac_fin.sweep_quiet(hs, p, A.shift(x, A.loads(hs), False{}), e, h)
    case T.Refused{why}:
      {==}

def ac_fin.part1(+b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +q: List<&2, Maybe<&2, Nat>>) -> {AgentCrown.ctook(A.hstep(b, A.Crown{t, hs}, A.OnTree{T.EvFinish{p, q}})) == AgentCrown.took(T.step(CS.bounds(b, A.Crown{t, hs}), CS.view(A.Crown{t, hs}), T.EvFinish{p, q})) : Bool}:
  %St.ac_step.bounds_eq(b, t, hs) : {AgentCrown.ctook(A.on_tree(T.step(A.cbounds(b, hs), A.view(t, hs), T.EvFinish{p, q}), hs, T.EvFinish{p, q})) == AgentCrown.took(T.step(_, CS.view_of(t, hs), T.EvFinish{p, q})) : Bool}
  %V.ac_view.view_eq(t, hs) : {AgentCrown.ctook(A.on_tree(T.step(A.cbounds(b, hs), A.view(t, hs), T.EvFinish{p, q}), hs, T.EvFinish{p, q})) == AgentCrown.took(T.step(A.cbounds(b, hs), _, T.EvFinish{p, q})) : Bool}
  ac_fin.took_on(T.step(A.cbounds(b, hs), A.view(t, hs), T.EvFinish{p, q}), hs, T.EvFinish{p, q})

def AgentCrown.crown_never_blocks(b, c, p, q):
  match c:
    case A.Crown{+t, +hs}:
      (ac_fin.part1(b, t, hs, p, q), ac_fin.quiet_on(T.step(A.cbounds(b, hs), A.view(t, hs), T.EvFinish{p, q}), hs, p, T.EvFinish{p, q}, ac_fin.step_stops(A.cbounds(b, hs), A.view(t, hs), p, q)))
