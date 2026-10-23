# eukhe: the proof of LAW wait_keeps_needed

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../laws/compactor.bend as Compactor
import ../base/logic/bool.bend as LLogicBool
import ../base/optchat.bend as LOptchat
import ./base.bend as LA

# a waiting turn stops no call it needs
def pc.implies_or(c: Bool, d: Bool, -y: Bool, e: {OBits.Bool.implies(c, y) == True{} : Bool}) -> {OBits.Bool.implies(c, Bool.or(d, y)) == True{} : Bool}:
  match c d:
    case False{} z:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      e

def pc.kept_cons(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>, +x: ONode.Node, +ws: List<&2, ONode.Node>, +e: {C.kept(info, v, bs, ws) == True{} : Bool}) -> {C.kept(info, v, bs, x <> ws) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +c = Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b)))
      +y = ONode.Nodes.has(ws, b)
      LA.pc.and_true(OBits.Bool.implies(c, Bool.or(ONode.Node.eq(x, b), y)), C.kept(info, v, rest, x <> ws), pc.implies_or(c, ONode.Node.eq(x, b), y, LLogicBool.pf.and_l(OBits.Bool.implies(c, y), C.kept(info, v, rest, ws), e)), pc.kept_cons(info, v, rest, x, ws, LLogicBool.pf.and_r(OBits.Bool.implies(c, y), C.kept(info, v, rest, ws), e)))

def pc.kept_step(c: Bool, +info: OInfo.Info, +v: List<&2, ONode.Node>, +b: ONode.Node, +rest: List<&2, ONode.Node>, +ns: List<&2, ONode.Node>, ih: {C.kept(info, v, rest, ns) == True{} : Bool}) -> {Bool.and(OBits.Bool.implies(c, ONode.Nodes.has(ONode.Nodes.keep(c, b, ns), b)), C.kept(info, v, rest, ONode.Nodes.keep(c, b, ns))) == True{} : Bool}:
  match c:
    case True{}:
      %LOptchat.pf.node_eq_refl(b) : {Bool.and(Bool.or(_, ONode.Nodes.has(ns, b)), C.kept(info, v, rest, b <> ns)) == True{} : Bool}
      pc.kept_cons(info, v, rest, b, ns, ih)
    case False{}:
      ih

def pc.kept_need(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> {C.kept(info, v, bs, OQueue.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.kept_step(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))), info, v, b, rest, OQueue.busy.need(info, v, rest), pc.kept_need(info, v, rest))

def pc.wait_keeps_needed(+s: OState.St) -> {C.kept(OState.St.info(s), OState.St.view(s), OState.St.busy(s), OState.St.busy(OQueue.St.wait(s))) == True{} : Bool}:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, +busy}:
      pc.kept_need(info, view, busy)

def Compactor.wait_keeps_needed(s):
  pc.wait_keeps_needed(s)
