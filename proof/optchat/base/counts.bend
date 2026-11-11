# eukhe: lemmas the proofs of area optchat share: counting nodes
#
# Naming one node by value (S.same: level and index value) is symmetric
# and transitive (cs.sym, cs.trans), and so is naming it exactly
# (S.key_same: level and index bits; cs.key_eq: then the nodes are
# equal). A removal of node n (ONode.Nodes.del) leaves no copy of n and
# every other node's count (cs.del); an addition (ONode.Nodes.add) gives
# n one copy when it had none (cs.add).

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../spec/memory/optchat.bend as S
import ../../base/nat.bend as LNat
import ./step.bend as LA
import ./queries.bend as LQ

# Logic
# -----

def cs.ne(-G: Type, -x: Bool, e1: {x == True{} : Bool}, e2: {x == False{} : Bool}) -> G:
  LA.cover.absurd(G, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, e2), e1))

def cs.zero0(b: Bool) -> {S.zero_if(b, 0n) == 0n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# One node by value
# -----------------

def cs.sym(a: ONode.Node, b: ONode.Node) -> {S.same(a, b) == S.same(b, a) : Bool}:
  match a b:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      %LNat.pt.eq_comm(lb, la) : {Bool.and(_, Nat.is_eq(OBits.Bits.val(ia), OBits.Bits.val(ib))) == S.same(ONode.Node{lb, ib}, ONode.Node{la, ia}) : Bool}
      %LNat.pt.eq_comm(OBits.Bits.val(ib), OBits.Bits.val(ia)) : {Bool.and(Nat.is_eq(lb, la), _) == S.same(ONode.Node{lb, ib}, ONode.Node{la, ia}) : Bool}
      {==}

def cs.sym_t(+a: ONode.Node, +b: ONode.Node, e: {S.same(a, b) == True{} : Bool}) -> {S.same(b, a) == True{} : Bool}:
  %cs.sym(a, b) : {_ == True{} : Bool}
  e

def cs.trans(a: ONode.Node, b: ONode.Node, c: ONode.Node, +e1: {S.same(a, b) == True{} : Bool}, +e2: {S.same(b, c) == True{} : Bool}) -> {S.same(a, c) == True{} : Bool}:
  match a b c:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib} ONode.Node{+lc, +ic}:
      +va = OBits.Bits.val(ia)
      +vb = OBits.Bits.val(ib)
      +vc = OBits.Bits.val(ic)
      +l1 = LA.cover.eq_of_is_eq(la, lb, LA.cover.and_l(Nat.is_eq(la, lb), Nat.is_eq(va, vb), e1))
      +v1 = LA.cover.eq_of_is_eq(va, vb, LA.cover.and_r(Nat.is_eq(la, lb), Nat.is_eq(va, vb), e1))
      +l2 = LA.cover.eq_of_is_eq(lb, lc, LA.cover.and_l(Nat.is_eq(lb, lc), Nat.is_eq(vb, vc), e2))
      +v2 = LA.cover.eq_of_is_eq(vb, vc, LA.cover.and_r(Nat.is_eq(lb, lc), Nat.is_eq(vb, vc), e2))
      %Equal.sym(Nat, la, lb, l1) : {Bool.and(Nat.is_eq(_, lc), Nat.is_eq(va, vc)) == True{} : Bool}
      %l2 : {Bool.and(Nat.is_eq(lb, _), Nat.is_eq(va, vc)) == True{} : Bool}
      %Equal.sym(Nat, va, vb, v1) : {Bool.and(Nat.is_eq(lb, lb), Nat.is_eq(_, vc)) == True{} : Bool}
      %v2 : {Bool.and(Nat.is_eq(lb, lb), Nat.is_eq(vb, _)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(lb, lb), True{}, LNat.child.pc.eq_refl(lb)) : {Bool.and(_, Nat.is_eq(vb, vb)) == True{} : Bool}
      LNat.child.pc.eq_refl(vb)

# One node exactly
# ----------------

def cs.bit_eq(x: Bool, y: Bool, e: {S.bit_same(x, y) == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      LA.cover.absurd({True{} == False{} : Bool}, e)
    case False{} True{}:
      LA.cover.absurd({False{} == True{} : Bool}, e)
    case False{} False{}:
      {==}

def cs.bits_eq(a: List<&2, Bool>, b: List<&2, Bool>, +e: {S.bits_same(a, b) == True{} : Bool}) -> {a == b : List<&2, Bool>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> ys:
      LA.cover.absurd({Nil{} == y <> ys : List<&2, Bool>}, e)
    case x <> xs Nil{}:
      LA.cover.absurd({x <> xs == Nil{} : List<&2, Bool>}, e)
    case +x <> +xs +y <> +ys:
      +hx = cs.bit_eq(x, y, LA.cover.and_l(S.bit_same(x, y), S.bits_same(xs, ys), e))
      +hxs = cs.bits_eq(xs, ys, LA.cover.and_r(S.bit_same(x, y), S.bits_same(xs, ys), e))
      %hx : {x <> xs == _ <> ys : List<&2, Bool>}
      %hxs : {x <> xs == x <> _ : List<&2, Bool>}
      {==}

# one key names one node
def cs.key_eq(n: ONode.Node, m: ONode.Node, +e: {S.key_same(n, m) == True{} : Bool}) -> {n == m : ONode.Node}:
  match n m:
    case ONode.Node{+l, +i} ONode.Node{+k, +j}:
      +hl = LA.cover.eq_of_is_eq(l, k, LA.cover.and_l(Nat.is_eq(l, k), S.bits_same(i, j), e))
      +hi = cs.bits_eq(i, j, LA.cover.and_r(Nat.is_eq(l, k), S.bits_same(i, j), e))
      %hl : {ONode.Node{l, i} == ONode.Node{_, j} : ONode.Node}
      %hi : {ONode.Node{l, i} == ONode.Node{l, _} : ONode.Node}
      {==}

# Counts
# ------

def cs.del_at(b1: Bool, b2: Bool, b3: Bool, +h: ONode.Node, +n: ONode.Node, +m: ONode.Node, -d: List<&2, ONode.Node>, -c: Nat,
  e1: {S.same(h, n) == b1 : Bool}, e2: {S.same(h, m) == b2 : Bool}, e3: {S.same(m, n) == b3 : Bool}, ih: {S.count(d, m) == S.zero_if(b3, c) : Nat})
  -> {S.count(ONode.Nodes.keep(Bool.not(b1), h, d), m) == S.zero_if(b3, S.one_if(b2, c)) : Nat}:
  match b1 b2 b3:
    case False{} False{} False{}:
      %Equal.sym(Bool, S.same(h, m), False{}, e2) : {S.one_if(_, S.count(d, m)) == c : Nat}
      ih
    case False{} False{} True{}:
      %Equal.sym(Bool, S.same(h, m), False{}, e2) : {S.one_if(_, S.count(d, m)) == 0n : Nat}
      ih
    case False{} True{} False{}:
      %Equal.sym(Bool, S.same(h, m), True{}, e2) : {S.one_if(_, S.count(d, m)) == 1n+c : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, S.count(d, m), c, ih)
    case False{} True{} True{}:
      cs.ne({S.count(ONode.Nodes.keep(True{}, h, d), m) == 0n : Nat}, S.same(h, n), cs.trans(h, m, n, e2, e3), e1)
    case True{} False{} False{}:
      ih
    case True{} False{} True{}:
      ih
    case True{} True{} False{}:
      cs.ne({S.count(d, m) == 1n+c : Nat}, S.same(m, n), cs.trans(m, h, n, cs.sym_t(h, m, e2), e1), e3)
    case True{} True{} True{}:
      ih

# removing n leaves no copy of n, and every other node's count
def cs.del(xs: List<&2, ONode.Node>, +n: ONode.Node, +m: ONode.Node) -> {S.count(ONode.Nodes.del(xs, n), m) == S.zero_if(S.same(m, n), S.count(xs, m)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, S.zero_if(S.same(m, n), 0n), 0n, cs.zero0(S.same(m, n)))
    case +h <> +t:
      %Equal.sym(Bool, ONode.Node.eq(h, n), S.same(h, n), LQ.oq.eq(h, n)) : {S.count(ONode.Nodes.keep(Bool.not(_), h, ONode.Nodes.del(t, n)), m) == S.zero_if(S.same(m, n), S.count(h <> t, m)) : Nat}
      cs.del_at(S.same(h, n), S.same(h, m), S.same(m, n), h, n, m, ONode.Nodes.del(t, n), S.count(t, m), {==}, {==}, {==}, cs.del(t, n, m))

def cs.add_at(b: Bool, +xs: List<&2, ONode.Node>, +n: ONode.Node, +m: ONode.Node, eb: {S.member(xs, n) == b : Bool})
  -> {S.count(ONode.Nodes.keep(Bool.not(b), n, xs), m) == S.one_if(Bool.and(S.same(m, n), Bool.not(b)), S.count(xs, m)) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.and(S.same(m, n), False{}), False{}, cs.and_false(S.same(m, n))) : {S.count(xs, m) == S.one_if(_, S.count(xs, m)) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Bool.and(S.same(m, n), True{}), S.same(m, n), cs.and_true(S.same(m, n))) : {S.one_if(S.same(n, m), S.count(xs, m)) == S.one_if(_, S.count(xs, m)) : Nat}
      %cs.sym(m, n) : {S.one_if(_, S.count(xs, m)) == S.one_if(S.same(m, n), S.count(xs, m)) : Nat}
      {==}

# adding n gives it one copy when it had none, and keeps every other count
def cs.add(+xs: List<&2, ONode.Node>, +n: ONode.Node, +m: ONode.Node) -> {S.count(ONode.Nodes.add(xs, n), m) == S.one_if(Bool.and(S.same(m, n), Bool.not(S.member(xs, n))), S.count(xs, m)) : Nat}:
  %Equal.sym(Bool, ONode.Nodes.has(xs, n), S.member(xs, n), LQ.oq.has(xs, n)) : {S.count(ONode.Nodes.keep(Bool.not(_), n, xs), m) == S.one_if(Bool.and(S.same(m, n), Bool.not(S.member(xs, n))), S.count(xs, m)) : Nat}
  cs.add_at(S.member(xs, n), xs, n, m, {==})
