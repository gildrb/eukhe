# eukhe: the proof of LAW need_first_due
# Under the mark a waiting turn's queue reads the view's leading lines
# before it, so every node it starts is such a line, unbuilt
# (LA.pc.cand_ok); each of them is a line of the whole view (nfd.has).

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../laws/compactor.bend as Compactor
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def nfd.or(x: Bool, -y: Bool, -z: Bool, e: {Bool.or(x, y) == True{} : Bool}, f: {y == True{} : Bool} -> {z == True{} : Bool}) -> {Bool.or(x, z) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      f(e)

def nfd.has.keep(go: Bool, +due: Nat, +h: ONode.Node, +rest: List<&2, ONode.Node>, +n: ONode.Node, e: {ONode.Nodes.has(OQueue.lines.keep(go, h, OQueue.lines.before(due, rest)), n) == True{} : Bool}, ih: {ONode.Nodes.has(OQueue.lines.before(due, rest), n) == True{} : Bool} -> {ONode.Nodes.has(rest, n) == True{} : Bool}) -> {Bool.or(ONode.Node.eq(h, n), ONode.Nodes.has(rest, n)) == True{} : Bool}:
  match go:
    case False{}:
      LLogicLogic.pf.absurd_ft({Bool.or(ONode.Node.eq(h, n), ONode.Nodes.has(rest, n)) == True{} : Bool}, e)
    case True{}:
      nfd.or(ONode.Node.eq(h, n), ONode.Nodes.has(OQueue.lines.before(due, rest), n), ONode.Nodes.has(rest, n), e, ih)

# a leading line before the mark is a line of the view
def nfd.has(v: List<&2, ONode.Node>, +due: Nat, +n: ONode.Node, e: {ONode.Nodes.has(OQueue.lines.before(due, v), n) == True{} : Bool}) -> {ONode.Nodes.has(v, n) == True{} : Bool}:
  match v:
    case Nil{}:
      e
    case +h <> +rest:
      nfd.has.keep(Nat.is_lt(ONode.Node.start(h), due), due, h, rest, n, e, hr => nfd.has(rest, due, n, hr))

# nodes that are unbuilt lines before the mark are unbuilt lines of the view
def nfd.needed(+info: OInfo.Info, +v: List<&2, ONode.Node>, +due: Nat, ns: List<&2, ONode.Node>, e: {C.needed(info, OQueue.lines.before(due, v), ns) == True{} : Bool}) -> {C.needed(info, v, ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      +lb = OQueue.lines.before(due, v)
      +nb = Bool.not(OInfo.Info.built(info, n))
      +e2 = e
      +ea = LLogicBool.pf.and_l(Bool.and(ONode.Nodes.has(lb, n), nb), C.needed(info, lb, rest), e2)
      LA.pc.and_true(Bool.and(ONode.Nodes.has(v, n), nb), C.needed(info, v, rest), LA.pc.and_true(ONode.Nodes.has(v, n), nb, nfd.has(v, due, n, LLogicBool.pf.and_l(ONode.Nodes.has(lb, n), nb, ea)), LLogicBool.pf.and_r(ONode.Nodes.has(lb, n), nb, ea)), nfd.needed(info, v, due, rest, LLogicBool.pf.and_r(Bool.and(ONode.Nodes.has(lb, n), nb), C.needed(info, lb, rest), e2)))

def nfd.go(+cfg: OState.Cfg, +due: Nat, s: OState.St) -> {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need.due(cfg, s, due)) == True{} : Bool}:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, +busy}:
      +lv = OQueue.lines.before(due, view)
      +jobs = OState.Cfg.jobs(cfg)
      +room = Nat.sub(jobs, List.length(&2, ONode.Node, busy))
      nfd.needed(info, view, due, OQueue.cand.view(lv, info, busy, jobs, 0n, room), LA.pc.cand_ok(lv, info, busy, jobs, 0n, room))

def Compactor.need_first_due(cfg, s, due):
  nfd.go(cfg, due, s)
