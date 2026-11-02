# eukhe: the proof of LAW due_keeps_all
# When every view line and every ready merge starts before the mark, the
# mark cuts none of them (dka.lines, dka.nodes): the chat the queue reads
# under it is the chat (dka.st), so both queries answer as without it.

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ../base/logic/bool.bend as LLogicBool

# the leading lines before the mark are all lines that start before it
def dka.lines(v: List<&2, ONode.Node>, +due: Nat, e: {S.starts_before(due, v) == True{} : Bool}) -> {OQueue.lines.before(due, v) == v : List<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +h <> +rest:
      +e2 = e
      +lt = Nat.is_lt(ONode.Node.start(h), due)
      %Equal.sym(Bool, lt, True{}, LLogicBool.pf.and_l(lt, S.starts_before(due, rest), e2)) : {OQueue.lines.keep(_, h, OQueue.lines.before(due, rest)) == h <> rest : List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node>, OQueue.lines.before(due, rest), rest, dka.lines(rest, due, LLogicBool.pf.and_r(lt, S.starts_before(due, rest), e2))) : {h <> _ == h <> rest : List<&2, ONode.Node>}
      {==}

# so are the merges before it
def dka.nodes(rs: List<&2, ONode.Node>, +due: Nat, e: {S.starts_before(due, rs) == True{} : Bool}) -> {OQueue.nodes.before(due, rs) == rs : List<&2, ONode.Node>}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +e2 = e
      +lt = Nat.is_lt(ONode.Node.start(h), due)
      %Equal.sym(Bool, lt, True{}, LLogicBool.pf.and_l(lt, S.starts_before(due, rest), e2)) : {ONode.Nodes.keep(_, h, OQueue.nodes.before(due, rest)) == h <> rest : List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node>, OQueue.nodes.before(due, rest), rest, dka.nodes(rest, due, LLogicBool.pf.and_r(lt, S.starts_before(due, rest), e2))) : {h <> _ == h <> rest : List<&2, ONode.Node>}
      {==}

# the chat under the mark is the chat
def dka.st(+due: Nat, s: OState.St, el: {S.starts_before(due, OState.St.view(s)) == True{} : Bool}, er: {S.starts_before(due, OState.St.ready(s)) == True{} : Bool}) -> {OQueue.St.due(due, s) == s : OState.St}:
  match s:
    case OState.St{+t, +info, +view, +shrink, +cview, +ready, +busy}:
      %Equal.sym(List<&2, ONode.Node>, OQueue.lines.before(due, view), view, dka.lines(view, due, el)) : {OState.St{t, info, _, shrink, cview, OQueue.nodes.before(due, ready), busy} == OState.St{t, info, view, shrink, cview, ready, busy} : OState.St}
      %Equal.sym(List<&2, ONode.Node>, OQueue.nodes.before(due, ready), ready, dka.nodes(ready, due, er)) : {OState.St{t, info, view, shrink, cview, _, busy} == OState.St{t, info, view, shrink, cview, ready, busy} : OState.St}
      {==}

def dka.go(+cfg: OState.Cfg, +due: Nat, +s: OState.St, el: {S.starts_before(due, OState.St.view(s)) == True{} : Bool}, er: {S.starts_before(due, OState.St.ready(s)) == True{} : Bool}) -> {OQueue.cands.due(cfg, s, due) == OQueue.cands(cfg, s) : List<&2, ONode.Node>} & {OQueue.cands.need.due(cfg, s, due) == OQueue.cands.need(cfg, s) : List<&2, ONode.Node>}:
  +e = dka.st(due, s, el, er)
  (Equal.cong(OState.St, List<&2, ONode.Node>, x => OQueue.cands(cfg, x), OQueue.St.due(due, s), s, e), Equal.cong(OState.St, List<&2, ONode.Node>, x => OQueue.cands.need(cfg, x), OQueue.St.due(due, s), s, e))

def Optchat.due_keeps_all(cfg, s, due, lines, merges):
  dka.go(cfg, due, s, lines, merges)
