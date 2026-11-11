# eukhe: the proof of LAW optchat_build_ready
# A build drops n from the ready merges (ONode.Nodes.del: a node is
# still there exactly when it was and is not n, br.del) and then, when
# n's sibling is built and its parent is not, inserts the parent
# (ONode.Nodes.ins: a node is there exactly when it was or is the parent,
# br.ins); naming one node by value is symmetric and transitive
# (LCs.cs.sym, LCs.cs.trans).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ
import ./base/counts.bend as LCs
import ./base/batch.bend as LB

# Bool
# ----

def br.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def br.or_rot(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, c), a) : Bool}:
  match a b c:
    case True{} True{} _:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def br.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Removal
# -------

def br.del_at(b1: Bool, b2: Bool, b3: Bool, +h: ONode.Node, +n: ONode.Node, +p: ONode.Node, -d: List<&2, ONode.Node>, +c: Bool,
  +e1: {S.same(h, n) == b1 : Bool}, +e2: {S.same(h, p) == b2 : Bool}, +e3: {S.same(p, n) == b3 : Bool}, ih: {S.member(d, p) == Bool.and(c, Bool.not(b3)) : Bool})
  -> {S.member(ONode.Nodes.keep(Bool.not(b1), h, d), p) == Bool.and(Bool.or(b2, c), Bool.not(b3)) : Bool}:
  match b1 b2 b3:
    case False{} False{} _:
      %Equal.sym(Bool, S.same(h, p), False{}, e2) : {Bool.or(_, S.member(d, p)) == Bool.and(c, Bool.not(b3)) : Bool}
      ih
    case False{} True{} False{}:
      %Equal.sym(Bool, S.same(h, p), True{}, e2) : {Bool.or(_, S.member(d, p)) == True{} : Bool}
      {==}
    case False{} True{} True{}:
      LCs.cs.ne({Bool.or(S.same(h, p), S.member(d, p)) == False{} : Bool}, S.same(h, n), LCs.cs.trans(h, p, n, e2, e3), e1)
    case True{} False{} False{}:
      ih
    case True{} True{} False{}:
      LCs.cs.ne({S.member(d, p) == True{} : Bool}, S.same(p, n), LCs.cs.trans(p, h, n, LCs.cs.sym_t(h, p, e2), e1), e3)
    case True{} _ True{}:
      Equal.trans(Bool, S.member(d, p), Bool.and(c, False{}), Bool.and(Bool.or(b2, c), False{}), ih, Equal.trans(Bool, Bool.and(c, False{}), False{}, Bool.and(Bool.or(b2, c), False{}), LCs.cs.and_false(c), Equal.sym(Bool, Bool.and(Bool.or(b2, c), False{}), False{}, LCs.cs.and_false(Bool.or(b2, c)))))

# after removing n, a node is there exactly when it was and is not n
def br.del(xs: List<&2, ONode.Node>, +n: ONode.Node, +p: ONode.Node) -> {S.member(ONode.Nodes.del(xs, n), p) == Bool.and(S.member(xs, p), Bool.not(S.same(p, n))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, ONode.Node.eq(h, n), S.same(h, n), LQ.oq.eq(h, n)) : {S.member(ONode.Nodes.keep(Bool.not(_), h, ONode.Nodes.del(t, n)), p) == Bool.and(S.member(h <> t, p), Bool.not(S.same(p, n))) : Bool}
      br.del_at(S.same(h, n), S.same(h, p), S.same(p, n), h, n, p, ONode.Nodes.del(t, n), S.member(t, p), {==}, {==}, {==}, br.del(t, n, p))

# Insertion
# ---------

def br.absorb(d: Bool, +h: ONode.Node, +x: ONode.Node, +p: ONode.Node, +c: Bool, +ed: {S.same(p, x) == d : Bool}, +sxh: {S.same(x, h) == True{} : Bool})
  -> {Bool.or(S.same(h, p), c) == Bool.or(Bool.or(S.same(h, p), c), d) : Bool}:
  match d:
    case False{}:
      Equal.sym(Bool, Bool.or(Bool.or(S.same(h, p), c), False{}), Bool.or(S.same(h, p), c), br.or_false(Bool.or(S.same(h, p), c)))
    case True{}:
      +shp = LCs.cs.sym_t(p, h, LCs.cs.trans(p, x, h, ed, sxh))
      %Equal.sym(Bool, S.same(h, p), True{}, shp) : {Bool.or(_, c) == Bool.or(Bool.or(_, c), True{}) : Bool}
      {==}

def br.ins_at(here: Bool, sm: Bool, +x: ONode.Node, +h: ONode.Node, +t: List<&2, ONode.Node>, +p: ONode.Node,
  esm: {ONode.Node.eq(x, h) == sm : Bool}, ih: {S.member(ONode.Nodes.ins(t, x), p) == Bool.or(S.member(t, p), S.same(p, x)) : Bool})
  -> {S.member(ONode.Nodes.ins.at(here, sm, x, h, t, ONode.Nodes.ins(t, x)), p) == Bool.or(Bool.or(S.same(h, p), S.member(t, p)), S.same(p, x)) : Bool}:
  match here sm:
    case True{} _:
      %LCs.cs.sym(p, x) : {Bool.or(_, Bool.or(S.same(h, p), S.member(t, p))) == Bool.or(Bool.or(S.same(h, p), S.member(t, p)), S.same(p, x)) : Bool}
      br.or_rot(S.same(p, x), S.same(h, p), S.member(t, p))
    case False{} True{}:
      +sxh = Equal.trans(Bool, S.same(x, h), ONode.Node.eq(x, h), True{}, Equal.sym(Bool, ONode.Node.eq(x, h), S.same(x, h), LQ.oq.eq(x, h)), esm)
      br.absorb(S.same(p, x), h, x, p, S.member(t, p), {==}, sxh)
    case False{} False{}:
      %Equal.sym(Bool, S.member(ONode.Nodes.ins(t, x), p), Bool.or(S.member(t, p), S.same(p, x)), ih) : {Bool.or(S.same(h, p), _) == Bool.or(Bool.or(S.same(h, p), S.member(t, p)), S.same(p, x)) : Bool}
      br.or_assoc(S.same(h, p), S.member(t, p), S.same(p, x))

# after inserting x, a node is there exactly when it was or is x
def br.ins(xs: List<&2, ONode.Node>, +x: ONode.Node, +p: ONode.Node) -> {S.member(ONode.Nodes.ins(xs, x), p) == Bool.or(S.member(xs, p), S.same(p, x)) : Bool}:
  match xs:
    case Nil{}:
      %LCs.cs.sym(p, x) : {Bool.or(_, False{}) == S.same(p, x) : Bool}
      br.or_false(S.same(p, x))
    case +h <> +t:
      br.ins_at(ONode.Node.lt(x, h), ONode.Node.eq(x, h), x, h, t, p, {==}, br.ins(t, x, p))

# The note
# --------

def br.note(g: Bool, +pn: ONode.Node, +ready: List<&2, ONode.Node>, +n: ONode.Node, +p: ONode.Node)
  -> {S.member(OStep.ready.if(g, pn, ONode.Nodes.del(ready, n)), p) == Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), Bool.and(S.same(p, pn), g)) : Bool}:
  match g:
    case False{}:
      %Equal.sym(Bool, Bool.and(S.same(p, pn), False{}), False{}, LCs.cs.and_false(S.same(p, pn))) : {S.member(ONode.Nodes.del(ready, n), p) == Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), _) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), False{}), Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), br.or_false(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))))) : {S.member(ONode.Nodes.del(ready, n), p) == _ : Bool}
      br.del(ready, n, p)
    case True{}:
      %Equal.sym(Bool, Bool.and(S.same(p, pn), True{}), S.same(p, pn), LCs.cs.and_true(S.same(p, pn))) : {S.member(ONode.Nodes.ins(ONode.Nodes.del(ready, n), pn), p) == Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), _) : Bool}
      Equal.trans(Bool, S.member(ONode.Nodes.ins(ONode.Nodes.del(ready, n), pn), p), Bool.or(S.member(ONode.Nodes.del(ready, n), p), S.same(p, pn)), Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), S.same(p, pn)),
        br.ins(ONode.Nodes.del(ready, n), pn, p),
        Equal.cong(Bool, Bool, q => Bool.or(q, S.same(p, pn)), S.member(ONode.Nodes.del(ready, n), p), Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), br.del(ready, n, p)))

def OptchatQueries.optchat_build_ready(cfg, s, n, size, p):
  match s:
    case OState.St{t, +info, view, shrink, cview, +ready, busy}:
      +info2 = OInfo.Info.set(info, n, size)
      %LB.ob.parent(n) : {S.member(OStep.ready.note(info2, n, ONode.Nodes.del(ready, n)), p) == Bool.or(Bool.and(S.member(ready, p), Bool.not(S.same(p, n))), Bool.and(S.same(p, _), Bool.and(OInfo.Info.built(info2, ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(info2, _))))) : Bool}
      br.note(Bool.and(OInfo.Info.built(info2, ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(info2, ONode.Node.parent(n)))), ONode.Node.parent(n), ready, n, p)
