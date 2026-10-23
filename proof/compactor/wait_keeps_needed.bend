# eukhe: the proof of LAW wait_keeps_needed

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat.bend as O
import ../../laws/compactor.bend as Compactor
import ../base/bool/and.bend as LBoolAnd
import ../base/optchat.bend as LOptchat
import ./base.bend as LA

# a waiting turn stops no call it needs
def pc.implies_or(c: Bool, d: Bool, -y: Bool, e: {O.Bool.implies(c, y) == True{} : Bool}) -> {O.Bool.implies(c, Bool.or(d, y)) == True{} : Bool}:
  match c d:
    case False{} z:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      e

def pc.kept_cons(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>, +x: O.Node, +ws: List<&2, O.Node>, +e: {C.kept(info, v, bs, ws) == True{} : Bool}) -> {C.kept(info, v, bs, x <> ws) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +c = Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b)))
      +y = O.Nodes.has(ws, b)
      LA.pc.and_true(O.Bool.implies(c, Bool.or(O.Node.eq(x, b), y)), C.kept(info, v, rest, x <> ws), pc.implies_or(c, O.Node.eq(x, b), y, LBoolAnd.pf.and_l(O.Bool.implies(c, y), C.kept(info, v, rest, ws), e)), pc.kept_cons(info, v, rest, x, ws, LBoolAnd.pf.and_r(O.Bool.implies(c, y), C.kept(info, v, rest, ws), e)))

def pc.kept_step(c: Bool, +info: O.Info, +v: List<&2, O.Node>, +b: O.Node, +rest: List<&2, O.Node>, +ns: List<&2, O.Node>, ih: {C.kept(info, v, rest, ns) == True{} : Bool}) -> {Bool.and(O.Bool.implies(c, O.Nodes.has(O.Nodes.keep(c, b, ns), b)), C.kept(info, v, rest, O.Nodes.keep(c, b, ns))) == True{} : Bool}:
  match c:
    case True{}:
      %LOptchat.pf.node_eq_refl(b) : {Bool.and(Bool.or(_, O.Nodes.has(ns, b)), C.kept(info, v, rest, b <> ns)) == True{} : Bool}
      pc.kept_cons(info, v, rest, b, ns, ih)
    case False{}:
      ih

def pc.kept_need(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>) -> {C.kept(info, v, bs, O.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.kept_step(Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))), info, v, b, rest, O.busy.need(info, v, rest), pc.kept_need(info, v, rest))

def pc.wait_keeps_needed(+s: O.St) -> {C.kept(O.St.info(s), O.St.view(s), O.St.busy(s), O.St.busy(O.St.wait(s))) == True{} : Bool}:
  match s:
    case O.St{t, +info, +view, shrink, cview, ready, +busy}:
      pc.kept_need(info, view, busy)

def Compactor.wait_keeps_needed(s):
  pc.wait_keeps_needed(s)
