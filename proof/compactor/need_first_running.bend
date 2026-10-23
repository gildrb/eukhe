# eukhe: the proof of LAW need_first_running

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../laws/compactor.bend as Compactor
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LA

# a waiting turn stops every call it does not need
def pc.keep_need(c: Bool, +info: OInfo.Info, +v: List<&2, ONode.Node>, +b: ONode.Node, +rest: List<&2, ONode.Node>, ec: {c == Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))) : Bool}, +ih: {C.needed(info, v, rest) == True{} : Bool}) -> {C.needed(info, v, ONode.Nodes.keep(c, b, rest)) == True{} : Bool}:
  match c:
    case True{}:
      %ec : {Bool.and(_, C.needed(info, v, rest)) == True{} : Bool}
      ih
    case False{}:
      ih

def pc.busy_need(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> {C.needed(info, v, OQueue.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.keep_need(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))), info, v, b, OQueue.busy.need(info, v, rest), {==}, pc.busy_need(info, v, rest))

def pc.needed_app(+info: OInfo.Info, +v: List<&2, ONode.Node>, xs: List<&2, ONode.Node>, -ys: List<&2, ONode.Node>, +ex: {C.needed(info, v, xs) == True{} : Bool}, +ey: {C.needed(info, v, ys) == True{} : Bool}) -> {C.needed(info, v, List.append(&2, ONode.Node, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ey
    case +x <> +rest:
      +a = Bool.and(ONode.Nodes.has(v, x), Bool.not(OInfo.Info.built(info, x)))
      LA.pc.and_true(a, C.needed(info, v, List.append(&2, ONode.Node, rest, ys)), LLogicBool.pf.and_l(a, C.needed(info, v, rest), ex), pc.needed_app(info, v, rest, ys, LLogicBool.pf.and_r(a, C.needed(info, v, rest), ex), ey))

def pc.need_first_running(+cfg: OState.Cfg, +s: OState.St) -> {C.needed(OState.St.info(s), OState.St.view(s), List.append(&2, ONode.Node, OState.St.busy(OQueue.St.wait(s)), OQueue.cands.need(cfg, OQueue.St.wait(s)))) == True{} : Bool}:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      +w = {OState.St{t, info, view, shrink, cview, ready, OQueue.busy.need(info, view, busy)} : OState.St}
      pc.needed_app(info, view, OQueue.busy.need(info, view, busy), OQueue.cands.need(cfg, w), pc.busy_need(info, view, busy), LA.pc.need_first(cfg, w))

def Compactor.need_first_running(cfg, s):
  pc.need_first_running(cfg, s)
