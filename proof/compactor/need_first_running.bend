# eukhe: the proof of LAW need_first_running

import Base
import ../../bend/optchat.bend as O
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# a waiting turn stops every call it does not need
def pc.keep_need(c: Bool, +info: O.Info, +v: List<&2, O.Node>, +b: O.Node, +rest: List<&2, O.Node>, ec: {c == Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))) : Bool}, +ih: {C.needed(info, v, rest) == True{} : Bool}) -> {C.needed(info, v, O.Nodes.keep(c, b, rest)) == True{} : Bool}:
  match c:
    case True{}:
      %ec : {Bool.and(_, C.needed(info, v, rest)) == True{} : Bool}
      ih
    case False{}:
      ih

def pc.busy_need(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>) -> {C.needed(info, v, O.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.keep_need(Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))), info, v, b, O.busy.need(info, v, rest), {==}, pc.busy_need(info, v, rest))

def pc.needed_app(+info: O.Info, +v: List<&2, O.Node>, xs: List<&2, O.Node>, -ys: List<&2, O.Node>, +ex: {C.needed(info, v, xs) == True{} : Bool}, +ey: {C.needed(info, v, ys) == True{} : Bool}) -> {C.needed(info, v, List.append(&2, O.Node, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ey
    case +x <> +rest:
      +a = Bool.and(O.Nodes.has(v, x), Bool.not(O.Info.built(info, x)))
      LA.pc.and_true(a, C.needed(info, v, List.append(&2, O.Node, rest, ys)), L.pf.and_l(a, C.needed(info, v, rest), ex), pc.needed_app(info, v, rest, ys, L.pf.and_r(a, C.needed(info, v, rest), ex), ey))

def pc.need_first_running(+cfg: O.Cfg, +s: O.St) -> {C.needed(O.St.info(s), O.St.view(s), List.append(&2, O.Node, O.St.busy(O.St.wait(s)), O.cands.need(cfg, O.St.wait(s)))) == True{} : Bool}:
  match s:
    case O.St{t, info, view, shrink, cview, ready, busy}:
      +w = {O.St{t, info, view, shrink, cview, ready, O.busy.need(info, view, busy)} : O.St}
      pc.needed_app(info, view, O.busy.need(info, view, busy), O.cands.need(cfg, w), pc.busy_need(info, view, busy), LA.pc.need_first(cfg, w))

def Laws.need_first_running(cfg, s):
  pc.need_first_running(cfg, s)
