# eukhe: the proof of LAW optchat_open_ready
# A spelled open opens the laws' open (LAO.oo.opened), which holds the
# ready merges its built nodes note (LAO.oo.holds). A node is in a list a
# node was inserted into when it is that node or was there before
# (ro.has_ins: an insert that finds an equal node keeps the list, and
# equal nodes are equal to the same nodes, ro.eq_same); so each built node
# adds its parent exactly when it is the parent of a built pair that is
# not built itself (ro.note, ro.ready).

import Base
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF
import ./base/open.bend as LAO
import ./base/step.bend as LAS

# Logic
# -----

def ro.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ro.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ro.or_false(a: Bool) -> {a == Bool.or(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ro.or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ro.or3(a: Bool, b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ro.or_twice(a: Bool, -b: Bool) -> {Bool.or(a, b) == Bool.or(a, Bool.or(a, b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Equal nodes
# -----------

# bit lists the same have equal values
def ro.same_is(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {OBits.Bits.same(xs, ys) == True{} : Bool}) -> {Nat.is_eq(OBits.Bits.val(xs), OBits.Bits.val(ys)) == True{} : Bool}:
  %LAS.pa.cmp_val(xs, ys) : {Cmp.is_eq(_) == True{} : Bool}
  e

def ro.same_val(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {OBits.Bits.same(xs, ys) == True{} : Bool}) -> {OBits.Bits.val(xs) == OBits.Bits.val(ys) : Nat}:
  LAS.cover.eq_of_is_eq(OBits.Bits.val(xs), OBits.Bits.val(ys), ro.same_is(xs, ys, e))

# a node equal to h is equal to the nodes h is equal to
def ro.eq_same(x: ONode.Node, h: ONode.Node, p: ONode.Node, +e: {ONode.Node.eq(x, h) == True{} : Bool}) -> {ONode.Node.eq(x, p) == ONode.Node.eq(h, p) : Bool}:
  match x h p:
    case ONode.Node{+lx, +ix} ONode.Node{+lh, +ih} ONode.Node{+lp, +ip}:
      +el = LAS.cover.eq_of_is_eq(lx, lh, LAF.oe.and_l(Nat.is_eq(lx, lh), OBits.Bits.same(ix, ih), e))
      +ev = ro.same_val(ix, ih, LAF.oe.and_r(Nat.is_eq(lx, lh), OBits.Bits.same(ix, ih), e))
      %Equal.sym(Nat, lx, lh, el) : {Bool.and(Nat.is_eq(_, lp), OBits.Bits.same(ix, ip)) == Bool.and(Nat.is_eq(lh, lp), OBits.Bits.same(ih, ip)) : Bool}
      %Equal.sym(Cmp, OBits.Bits.cmp(ix, ip), Nat.cmp(OBits.Bits.val(ix), OBits.Bits.val(ip)), LAS.pa.cmp_val(ix, ip)) : {Bool.and(Nat.is_eq(lh, lp), Cmp.is_eq(_)) == Bool.and(Nat.is_eq(lh, lp), OBits.Bits.same(ih, ip)) : Bool}
      %Equal.sym(Cmp, OBits.Bits.cmp(ih, ip), Nat.cmp(OBits.Bits.val(ih), OBits.Bits.val(ip)), LAS.pa.cmp_val(ih, ip)) : {Bool.and(Nat.is_eq(lh, lp), Cmp.is_eq(Nat.cmp(OBits.Bits.val(ix), OBits.Bits.val(ip)))) == Bool.and(Nat.is_eq(lh, lp), Cmp.is_eq(_)) : Bool}
      %Equal.sym(Nat, OBits.Bits.val(ix), OBits.Bits.val(ih), ev) : {Bool.and(Nat.is_eq(lh, lp), Cmp.is_eq(Nat.cmp(_, OBits.Bits.val(ip)))) == Bool.and(Nat.is_eq(lh, lp), Cmp.is_eq(Nat.cmp(OBits.Bits.val(ih), OBits.Bits.val(ip)))) : Bool}
      {==}

# Insert
# ------

def ro.ins_at(here: Bool, same: Bool, +x: ONode.Node, +h: ONode.Node, +t: List<&2, ONode.Node>, -rec: List<&2, ONode.Node>, +p: ONode.Node, se: {same == ONode.Node.eq(x, h) : Bool}, ih: {ONode.Nodes.has(rec, p) == Bool.or(ONode.Node.eq(x, p), ONode.Nodes.has(t, p)) : Bool}) -> {ONode.Nodes.has(ONode.Nodes.ins.at(here, same, x, h, t, rec), p) == Bool.or(ONode.Node.eq(x, p), Bool.or(ONode.Node.eq(h, p), ONode.Nodes.has(t, p))) : Bool}:
  match here same:
    case True{} _:
      {==}
    case False{} True{}:
      %Equal.sym(Bool, ONode.Node.eq(x, p), ONode.Node.eq(h, p), ro.eq_same(x, h, p, Equal.sym(Bool, True{}, ONode.Node.eq(x, h), se))) : {Bool.or(ONode.Node.eq(h, p), ONode.Nodes.has(t, p)) == Bool.or(_, Bool.or(ONode.Node.eq(h, p), ONode.Nodes.has(t, p))) : Bool}
      ro.or_twice(ONode.Node.eq(h, p), ONode.Nodes.has(t, p))
    case False{} False{}:
      %Equal.sym(Bool, ONode.Nodes.has(rec, p), Bool.or(ONode.Node.eq(x, p), ONode.Nodes.has(t, p)), ih) : {Bool.or(ONode.Node.eq(h, p), _) == Bool.or(ONode.Node.eq(x, p), Bool.or(ONode.Node.eq(h, p), ONode.Nodes.has(t, p))) : Bool}
      ro.or_swap(ONode.Node.eq(h, p), ONode.Node.eq(x, p), ONode.Nodes.has(t, p))

# a node is in a list x was inserted into when it is x or was there
def ro.has_ins(xs: List<&2, ONode.Node>, +x: ONode.Node, +p: ONode.Node) -> {ONode.Nodes.has(ONode.Nodes.ins(xs, x), p) == Bool.or(ONode.Node.eq(x, p), ONode.Nodes.has(xs, p)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      ro.ins_at(ONode.Node.lt(x, h), ONode.Node.eq(x, h), x, h, t, ONode.Nodes.ins(t, x), p, {==}, ro.has_ins(t, x, p))

# The ready merges
# ----------------

# a built node noted: its parent is in the ready merges when it was, or
# when it is the parent and the note's condition holds
def ro.note(c: Bool, +par: ONode.Node, +rs: List<&2, ONode.Node>, +p: ONode.Node, +r: Bool) -> {Bool.or(ONode.Nodes.has(OStep.ready.if(c, par, rs), p), r) == Bool.or(ONode.Nodes.has(rs, p), Bool.or(Bool.and(ONode.Node.eq(par, p), c), r)) : Bool}:
  match c:
    case False{}:
      %Equal.sym(Bool, Bool.and(ONode.Node.eq(par, p), False{}), False{}, ro.and_false(ONode.Node.eq(par, p))) : {Bool.or(ONode.Nodes.has(rs, p), r) == Bool.or(ONode.Nodes.has(rs, p), Bool.or(_, r)) : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, ONode.Nodes.has(ONode.Nodes.ins(rs, par), p), Bool.or(ONode.Node.eq(par, p), ONode.Nodes.has(rs, p)), ro.has_ins(rs, par, p)) : {Bool.or(_, r) == Bool.or(ONode.Nodes.has(rs, p), Bool.or(Bool.and(ONode.Node.eq(par, p), True{}), r)) : Bool}
      %Equal.sym(Bool, Bool.and(ONode.Node.eq(par, p), True{}), ONode.Node.eq(par, p), ro.and_true(ONode.Node.eq(par, p))) : {Bool.or(Bool.or(ONode.Node.eq(par, p), ONode.Nodes.has(rs, p)), r) == Bool.or(ONode.Nodes.has(rs, p), Bool.or(_, r)) : Bool}
      ro.or3(ONode.Node.eq(par, p), ONode.Nodes.has(rs, p), r)

# the ready merges after the built nodes bs: those before, and the
# parents of built pairs of bs that are not built
def ro.ready(bs: List<&2, FOc.Got>, +info: OInfo.Info, +rs: List<&2, ONode.Node>, +p: ONode.Node) -> {ONode.Nodes.has(Optchat.oc_ready(bs, info, rs), p) == Bool.or(ONode.Nodes.has(rs, p), Optchat.oc_pair_of(info, bs, p)) : Bool}:
  match bs:
    case Nil{}:
      ro.or_false(ONode.Nodes.has(rs, p))
    case FOc.Got{+l, +k, z} <> +rest:
      +n = Optchat.oc_node(l, k)
      +note = OStep.ready.note(info, n, rs)
      %Equal.sym(Bool, ONode.Nodes.has(Optchat.oc_ready(rest, info, note), p), Bool.or(ONode.Nodes.has(note, p), Optchat.oc_pair_of(info, rest, p)), ro.ready(rest, info, note, p)) : {_ == Bool.or(ONode.Nodes.has(rs, p), Optchat.oc_pair_of(info, FOc.Got{l, k, z} <> rest, p)) : Bool}
      ro.note(Bool.and(OInfo.Info.built(info, ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(info, ONode.Node.parent(n)))), ONode.Node.parent(n), rs, p, Optchat.oc_pair_of(info, rest, p))

def ro.main(+o: FOc.Open, +p: ONode.Node, fits: {Optchat.oc_open_fits(o) == True{} : Bool}) -> {ONode.Nodes.has(OState.St.ready(Optchat.oc_chat(Optchat.oc_state(FOc.open(Optchat.oc_spell_open(o))))), p) == Optchat.oc_pair_of(Optchat.oc_info(Optchat.oc_built(o), OInfo.Info.empty()), Optchat.oc_built(o), p) : Bool}:
  +info = Optchat.oc_info(Optchat.oc_built(o), OInfo.Info.empty())
  %Equal.sym(FOc.St & String, FOc.open(Optchat.oc_spell_open(o)), Optchat.oc_open_model(o), LAO.oo.opened(o, fits)) : {ONode.Nodes.has(OState.St.ready(Optchat.oc_chat(Optchat.oc_state(_))), p) == Optchat.oc_pair_of(info, Optchat.oc_built(o), p) : Bool}
  %Equal.sym(List<&2, ONode.Node>, OState.St.ready(Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))), Optchat.oc_ready(Optchat.oc_built(o), info, Nil{}), LAO.oo.holds(o)) : {ONode.Nodes.has(_, p) == Optchat.oc_pair_of(info, Optchat.oc_built(o), p) : Bool}
  ro.ready(Optchat.oc_built(o), info, Nil{}, p)

def Optchat.optchat_open_ready(o, p, fits):
  ro.main(o, p, fits)
