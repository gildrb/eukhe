# eukhe: the proof of LAW optchat_start_counts
# A start sets the busy calls to ONode.Nodes.add(busy, n) and nothing
# else (sc.set); adding n gives it one call when it had none and keeps
# every other count (LCs.cs.add).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/counts.bend as LCs

def sc.set(s: OState.St, -bs: List<&2, ONode.Node>) -> {OStep.busy.set(s, bs) == S.with_busy(s, OState.St.busy(OStep.busy.set(s, bs))) : OState.St}:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      {==}

def sc.busy(s: OState.St, -bs: List<&2, ONode.Node>) -> {OState.St.busy(OStep.busy.set(s, bs)) == bs : List<&2, ONode.Node>}:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      {==}

def sc.count(+s: OState.St, +n: ONode.Node, +m: ONode.Node) -> {S.count(OState.St.busy(OStep.busy.set(s, ONode.Nodes.add(OState.St.busy(s), n))), m) == S.one_if(Bool.and(S.same(m, n), Bool.not(S.member(OState.St.busy(s), n))), S.count(OState.St.busy(s), m)) : Nat}:
  +d = ONode.Nodes.add(OState.St.busy(s), n)
  %Equal.sym(List<&2, ONode.Node>, OState.St.busy(OStep.busy.set(s, d)), d, sc.busy(s, d)) : {S.count(_, m) == S.one_if(Bool.and(S.same(m, n), Bool.not(S.member(OState.St.busy(s), n))), S.count(OState.St.busy(s), m)) : Nat}
  LCs.cs.add(OState.St.busy(s), n, m)

def OptchatQueries.optchat_start_counts(cfg, s, n, m):
  (sc.set(s, ONode.Nodes.add(OState.St.busy(s), n)), ({==}, sc.count(s, n, m)))
