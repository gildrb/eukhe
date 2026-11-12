# eukhe: the proof of LAW optchat_free_counts
# A free sets the busy calls to ONode.Nodes.del(busy, n) and nothing else
# (fc.set); removing n leaves no copy of it and every other count
# (LCs.cs.del).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/counts.bend as LCs

def fc.set(s: OState.St, -bs: List<&2, ONode.Node>) -> {OStep.busy.set(s, bs) == S.with_busy(s, OState.St.busy(OStep.busy.set(s, bs))) : OState.St}:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      {==}

def fc.busy(s: OState.St, -bs: List<&2, ONode.Node>) -> {OState.St.busy(OStep.busy.set(s, bs)) == bs : List<&2, ONode.Node>}:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      {==}

def fc.count(+s: OState.St, +n: ONode.Node, +m: ONode.Node) -> {S.count(OState.St.busy(OStep.busy.set(s, ONode.Nodes.del(OState.St.busy(s), n))), m) == S.zero_if(S.same(m, n), S.count(OState.St.busy(s), m)) : Nat}:
  +d = ONode.Nodes.del(OState.St.busy(s), n)
  %Equal.sym(List<&2, ONode.Node>, OState.St.busy(OStep.busy.set(s, d)), d, fc.busy(s, d)) : {S.count(_, m) == S.zero_if(S.same(m, n), S.count(OState.St.busy(s), m)) : Nat}
  LCs.cs.del(OState.St.busy(s), n, m)

def OptchatQueries.optchat_free_counts(cfg, s, n, m):
  (fc.set(s, ONode.Nodes.del(OState.St.busy(s), n)), ({==}, fc.count(s, n, m)))
