# eukhe: the proof of LAW optchat_wait_keeps_needed
# A wait splits the busy calls by one test per call (needed: a view line,
# unbuilt): the kept ones (busy.need) and the answered ones (busy.held).
# Per node m, a call of m is m itself (LCs.cs.key_eq), so the test on it
# is m's (wk.link): m's calls stay when m is needed, else none
# (wk.need); each call lands in exactly one of the two lists (wk.sum).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/queue.bend as OQueue
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/step.bend as LA
import ./base/queries.bend as LQ
import ./base/counts.bend as LCs
import ./base/bits.bend as LAB

# a kept line's count of m, from the rest's
def wk.kc(k: Bool, ks: Bool, c: Nat) -> Nat:
  match k:
    case True{}:
      S.one_if(ks, c)
    case False{}:
      c

def wk.keep(k: Bool, +b: ONode.Node, +m: ONode.Node, -r: List<&2, ONode.Node>) -> {wk.kc(k, S.key_same(b, m), S.copies(r, m)) == S.copies(ONode.Nodes.keep(k, b, r), m) : Nat}:
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

def wk.notnot(x: Bool) -> {Bool.not(Bool.not(x)) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# the kept count: m's when needed (the test kb on a call of m is not z)
def wk.step(kb: Bool, ks: Bool, z: Bool, -cr: Nat, -c: Nat, ih: {cr == S.zero_if(z, c) : Nat}, link: {ks == True{} : Bool} -> {kb == Bool.not(z) : Bool}) -> {wk.kc(kb, ks, cr) == S.zero_if(z, S.one_if(ks, c)) : Nat}:
  match kb ks z:
    case True{} True{} True{}:
      LA.cover.absurd({1n+cr == 0n : Nat}, Equal.sym(Bool, True{}, False{}, link({==})))
    case True{} True{} False{}:
      Equal.cong(Nat, Nat, x => 1n+x, cr, c, ih)
    case True{} False{} _:
      ih
    case False{} True{} True{}:
      ih
    case False{} True{} False{}:
      LA.cover.absurd({cr == 1n+c : Nat}, link({==}))
    case False{} False{} _:
      ih

# the calls of m kept plus the calls of m answered
def wk.sumv(kb: Bool, ks: Bool, +h: Nat, +n: Nat, -c: Nat, ih: {Nat.add(h, n) == c : Nat}) -> {Nat.add(wk.kc(Bool.not(kb), ks, h), wk.kc(kb, ks, n)) == S.one_if(ks, c) : Nat}:
  match kb ks:
    case True{} True{}:
      %Equal.sym(Nat, Nat.add(h, 1n+n), 1n+Nat.add(h, n), LAB.ob.add_succ(h, n)) : {_ == 1n+c : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(h, n), c, ih)
    case True{} False{}:
      ih
    case False{} True{}:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(h, n), c, ih)
    case False{} False{}:
      ih

# a call of m tests as m
def wk.link(+info: OInfo.Info, +v: List<&2, ONode.Node>, +b: ONode.Node, +m: ONode.Node, e: {S.key_same(b, m) == True{} : Bool}) -> {Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))) == Bool.not(Bool.not(Bool.and(S.member(v, m), Bool.not(OInfo.Info.built(info, m))))) : Bool}:
  %LCs.cs.key_eq(b, m, e) : {Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))) == Bool.not(Bool.not(Bool.and(S.member(v, _), Bool.not(OInfo.Info.built(info, _))))) : Bool}
  %Equal.sym(Bool, ONode.Nodes.has(v, b), S.member(v, b), LQ.oq.has(v, b)) : {Bool.and(_, Bool.not(OInfo.Info.built(info, b))) == Bool.not(Bool.not(Bool.and(S.member(v, b), Bool.not(OInfo.Info.built(info, b))))) : Bool}
  Equal.sym(Bool, Bool.not(Bool.not(Bool.and(S.member(v, b), Bool.not(OInfo.Info.built(info, b))))), Bool.and(S.member(v, b), Bool.not(OInfo.Info.built(info, b))), wk.notnot(Bool.and(S.member(v, b), Bool.not(OInfo.Info.built(info, b)))))

def wk.need(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>, +m: ONode.Node) -> {S.copies(OQueue.busy.need(info, v, bs), m) == S.zero_if(Bool.not(Bool.and(S.member(v, m), Bool.not(OInfo.Info.built(info, m)))), S.copies(bs, m)) : Nat}:
  match bs:
    case Nil{}:
      Equal.sym(Nat, S.zero_if(Bool.not(Bool.and(S.member(v, m), Bool.not(OInfo.Info.built(info, m)))), 0n), 0n, LCs.cs.zero0(Bool.not(Bool.and(S.member(v, m), Bool.not(OInfo.Info.built(info, m))))))
    case +b <> +rest:
      +kb = Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b)))
      +z = Bool.not(Bool.and(S.member(v, m), Bool.not(OInfo.Info.built(info, m))))
      +r = OQueue.busy.need(info, v, rest)
      %wk.keep(kb, b, m, r) : {_ == S.zero_if(z, S.one_if(S.key_same(b, m), S.copies(rest, m))) : Nat}
      wk.step(kb, S.key_same(b, m), z, S.copies(r, m), S.copies(rest, m), wk.need(info, v, rest, m), e => wk.link(info, v, b, m, e))

def wk.sum(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>, +m: ONode.Node) -> {Nat.add(S.copies(OQueue.busy.held(info, v, bs), m), S.copies(OQueue.busy.need(info, v, bs), m)) == S.copies(bs, m) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +kb = Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b)))
      +h = OQueue.busy.held(info, v, rest)
      +n = OQueue.busy.need(info, v, rest)
      %wk.keep(Bool.not(kb), b, m, h) : {Nat.add(_, S.copies(ONode.Nodes.keep(kb, b, n), m)) == S.one_if(S.key_same(b, m), S.copies(rest, m)) : Nat}
      %wk.keep(kb, b, m, n) : {Nat.add(wk.kc(Bool.not(kb), S.key_same(b, m), S.copies(h, m)), _) == S.one_if(S.key_same(b, m), S.copies(rest, m)) : Nat}
      wk.sumv(kb, S.key_same(b, m), S.copies(h, m), S.copies(n, m), S.copies(rest, m), wk.sum(info, v, rest, m))

def OptchatQueries.optchat_wait_keeps_needed(s, m):
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, +busy}:
      ({==}, (wk.need(info, view, busy, m), wk.sum(info, view, busy, m)))
