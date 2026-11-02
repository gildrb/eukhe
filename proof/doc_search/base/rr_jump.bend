# eukhe: lemmas of the match limit's jumps (bend/doc_search.bend rr.fast):
# d full rounds from round r are the spec's d rounds (DocSearch.ds_rounds)
# when the budget pays for them and every file holds at most r matches or
# at least r + d (rr.clear)

import Base
import ../../../bend/doc_search.bend as Sr
import ../../../laws/doc_search.bend as DocSearch

# Logic and Nats
# --------------

def rj.BD(b: Bool, A: Type, B: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      B

# False is not True: anything follows
def rj.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rj.BD(_, A, Unit)
  Unit{}

def rj.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rj.ft({False{} == True{} : Bool}, e)

def rj.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rj.ft({b == True{} : Bool}, e)

def rj.sub0(n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rj.add0(n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %rj.add0(p) : {1n+p == 1n+_ : Nat}
      {==}

def rj.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, 1n+Nat.add(p, b), Nat.add(p, 1n+b), rj.add_succ(p, b))

def rj.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), rj.add_assoc(p, b, c))

def rj.subsub(b: Nat, a: Nat, -x: Nat) -> {Nat.sub(Nat.sub(b, a), x) == Nat.sub(b, Nat.add(a, x)) : Nat}:
  match b a:
    case 0n 0n:
      {==}
    case 1n+q 0n:
      {==}
    case 0n 1n+p:
      {==}
    case 1n+q 1n+p:
      rj.subsub(q, p, x)

def rj.min0(x: Nat) -> {0n == Nat.min(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# z <= x - n when n + z <= x
def rj.le_sub(n: Nat, -z: Nat, x: Nat, e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      rj.ft({Nat.is_le(z, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      rj.le_sub(p, z, q, e)

# n <= x when n + z <= x
def rj.le_add(n: Nat, -z: Nat, x: Nat, e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      rj.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      rj.le_add(p, z, q, e)

# Lists of counts
# ---------------

# a full round from round r: one for each file with more than r matches
def rj.ind(cs: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      Sr.rr.one(Nat.is_lt(r, c)) <> rj.ind(t, r)

def rj.plus_assoc(xs: List<&2, Nat>, ys: List<&2, Nat>, zs: List<&2, Nat>) -> {DocSearch.ds_plus(DocSearch.ds_plus(xs, ys), zs) == DocSearch.ds_plus(xs, DocSearch.ds_plus(ys, zs)) : List<&2, Nat>}:
  match xs ys zs:
    case Nil{} ys zs:
      {==}
    case x <> t Nil{} zs:
      {==}
    case x <> t y <> u Nil{}:
      {==}
    case +x <> t +y <> u +z <> v:
      %rj.add_assoc(x, y, z) : {Nat.add(Nat.add(x, y), z) <> DocSearch.ds_plus(DocSearch.ds_plus(t, u), v) == _ <> DocSearch.ds_plus(t, DocSearch.ds_plus(u, v)) : List<&2, Nat>}
      %rj.plus_assoc(t, u, v) : {Nat.add(Nat.add(x, y), z) <> DocSearch.ds_plus(DocSearch.ds_plus(t, u), v) == Nat.add(Nat.add(x, y), z) <> _ : List<&2, Nat>}
      {==}

# no matches kept, then a round: the round
def rj.zero_round(cs: List<&2, Nat>, +r: Nat, +b: Nat) -> {DocSearch.ds_plus(Sr.rr.zeros(cs), DocSearch.ds_round(cs, r, b)) == DocSearch.ds_round(cs, r, b) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      +g = DocSearch.ds_bit(Bool.and(Nat.is_lt(0n, b), Nat.is_lt(r, c)))
      %rj.zero_round(t, r, Nat.sub(b, g)) : {g <> DocSearch.ds_plus(Sr.rr.zeros(t), DocSearch.ds_round(t, r, Nat.sub(b, g))) == g <> _ : List<&2, Nat>}
      {==}

def rj.zero_rounds(f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat) -> {DocSearch.ds_plus(Sr.rr.zeros(cs), DocSearch.ds_rounds(f, cs, r, b)) == DocSearch.ds_rounds(f, cs, r, b) : List<&2, Nat>}:
  match f:
    case 0n:
      rj.zero_round(cs, r, 0n)
    case 1n+g:
      +z = Sr.rr.zeros(cs)
      +x = DocSearch.ds_round(cs, r, b)
      +y = DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(b, DocSearch.ds_sum(x)))
      %rj.plus_assoc(z, x, y) : {_ == DocSearch.ds_plus(x, y) : List<&2, Nat>}
      %rj.zero_round(cs, r, b) : {DocSearch.ds_plus(DocSearch.ds_plus(z, x), y) == DocSearch.ds_plus(_, y) : List<&2, Nat>}
      {==}

def rj.block0(cs: List<&2, Nat>, +r: Nat) -> {Sr.rr.zeros(cs) == Sr.rr.block(cs, r, 0n) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %rj.min0(Nat.sub(c, r)) : {0n <> Sr.rr.zeros(t) == _ <> Sr.rr.block(t, r, 0n) : List<&2, Nat>}
      %rj.block0(t, r) : {0n <> Sr.rr.zeros(t) == 0n <> _ : List<&2, Nat>}
      {==}

# one file: d + 1 rounds from r give one in round r, then d from r + 1
def rj.block_el(c: Nat, r: Nat, +d: Nat) -> {Nat.min(Nat.sub(c, r), 1n+d) == Nat.add(Sr.rr.one(Nat.is_lt(r, c)), Nat.min(Nat.sub(c, 1n+r), d)) : Nat}:
  match c r:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n++p 0n:
      %rj.sub0(p) : {1n+Nat.min(p, d) == 1n+Nat.min(_, d) : Nat}
      {==}
    case 1n+p 1n+q:
      rj.block_el(p, q, d)

def rj.block_step(cs: List<&2, Nat>, +r: Nat, +d: Nat) -> {DocSearch.ds_plus(rj.ind(cs, r), Sr.rr.block(cs, 1n+r, d)) == Sr.rr.block(cs, r, 1n+d) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      %rj.block_el(c, r, d) : {_ <> DocSearch.ds_plus(rj.ind(t, r), Sr.rr.block(t, 1n+r, d)) == Nat.min(Nat.sub(c, r), 1n+d) <> Sr.rr.block(t, r, 1n+d) : List<&2, Nat>}
      %rj.block_step(t, r, d) : {Nat.min(Nat.sub(c, r), 1n+d) <> DocSearch.ds_plus(rj.ind(t, r), Sr.rr.block(t, 1n+r, d)) == Nat.min(Nat.sub(c, r), 1n+d) <> _ : List<&2, Nat>}
      {==}

def rj.sum_ind(cs: List<&2, Nat>, +r: Nat) -> {Sr.rr.act(cs, r) == DocSearch.ds_sum(rj.ind(cs, r)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      %rj.sum_ind(t, r) : {Nat.add(Sr.rr.one(Nat.is_lt(r, c)), Sr.rr.act(t, r)) == Nat.add(Sr.rr.one(Nat.is_lt(r, c)), _) : Nat}
      {==}

# Full rounds
# -----------

def rj.full.k(x: Bool, b: Nat, +t: List<&2, Nat>, +r: Nat, ih: @b2:Nat -> {Nat.is_le(Sr.rr.act(t, r), b2) == True{} : Bool} -> {rj.ind(t, r) == DocSearch.ds_round(t, r, b2) : List<&2, Nat>}, h: {Nat.is_le(Nat.add(Sr.rr.one(x), Sr.rr.act(t, r)), b) == True{} : Bool}) -> {Sr.rr.one(x) <> rj.ind(t, r) == DocSearch.ds_bit(Bool.and(Nat.is_lt(0n, b), x)) <> DocSearch.ds_round(t, r, Nat.sub(b, DocSearch.ds_bit(Bool.and(Nat.is_lt(0n, b), x)))) : List<&2, Nat>}:
  match x b:
    case True{} 0n:
      rj.ft({1n <> rj.ind(t, r) == 0n <> DocSearch.ds_round(t, r, 0n) : List<&2, Nat>}, h)
    case True{} 1n++q:
      %rj.sub0(q) : {1n <> rj.ind(t, r) == 1n <> DocSearch.ds_round(t, r, _) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => 1n <> xs, rj.ind(t, r), DocSearch.ds_round(t, r, q), ih(q, h))
    case False{} 0n:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => 0n <> xs, rj.ind(t, r), DocSearch.ds_round(t, r, 0n), ih(0n, h))
    case False{} 1n++q:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => 0n <> xs, rj.ind(t, r), DocSearch.ds_round(t, r, 1n+q), ih(1n+q, h))

# a budget that pays a round: the round gives each file with more than r
# matches one
def rj.full(cs: List<&2, Nat>, +r: Nat, b: Nat, h: {Nat.is_le(Sr.rr.act(cs, r), b) == True{} : Bool}) -> {rj.ind(cs, r) == DocSearch.ds_round(cs, r, b) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      rj.full.k(Nat.is_lt(r, c), b, t, r, b2 => h2 => rj.full(t, r, b2, h2), h)

# Clear rounds
# ------------

def rj.act_el(c: Nat, r: Nat, -e: Nat, h: {Bool.or(Nat.is_le(c, r), Nat.is_le(Nat.add(r, 2n+e), c)) == True{} : Bool}) -> {Nat.is_lt(1n+r, c) == Nat.is_lt(r, c) : Bool}:
  match c r:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n 0n:
      rj.ft({Nat.is_lt(1n, 1n) == Nat.is_lt(0n, 1n) : Bool}, h)
    case 2n+u 0n:
      {==}
    case 1n+p 1n+q:
      rj.act_el(p, q, e, h)

def rj.act(cs: List<&2, Nat>, +r: Nat, +e: Nat, +h: {Sr.rr.clear(cs, r, 2n+e) == True{} : Bool}) -> {Sr.rr.act(cs, 1n+r) == Sr.rr.act(cs, r) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      +x = Bool.or(Nat.is_le(c, r), Nat.is_le(Nat.add(r, 2n+e), c))
      %rj.act_el(c, r, e, rj.and_l(x, Sr.rr.clear(t, r, 2n+e), h)) : {Nat.add(Sr.rr.one(Nat.is_lt(1n+r, c)), Sr.rr.act(t, 1n+r)) == Nat.add(Sr.rr.one(_), Sr.rr.act(t, r)) : Nat}
      %rj.act(t, r, e, rj.and_r(x, Sr.rr.clear(t, r, 2n+e), h)) : {Nat.add(Sr.rr.one(Nat.is_lt(1n+r, c)), Sr.rr.act(t, 1n+r)) == Nat.add(Sr.rr.one(Nat.is_lt(1n+r, c)), _) : Nat}
      {==}

def rj.clear_el(c: Nat, r: Nat, -e: Nat, h: {Bool.or(Nat.is_le(c, r), Nat.is_le(Nat.add(r, 2n+e), c)) == True{} : Bool}) -> {Bool.or(Nat.is_le(c, 1n+r), Nat.is_le(Nat.add(1n+r, 1n+e), c)) == True{} : Bool}:
  match c r:
    case 0n r:
      {==}
    case 1n 0n:
      {==}
    case 2n+u 0n:
      h
    case 1n+p 1n+q:
      rj.clear_el(p, q, e, h)

def rj.clear(cs: List<&2, Nat>, +r: Nat, +e: Nat, +h: {Sr.rr.clear(cs, r, 2n+e) == True{} : Bool}) -> {Sr.rr.clear(cs, 1n+r, 1n+e) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      +x = Bool.or(Nat.is_le(c, r), Nat.is_le(Nat.add(r, 2n+e), c))
      +y = Bool.or(Nat.is_le(c, 1n+r), Nat.is_le(Nat.add(1n+r, 1n+e), c))
      +hx = rj.clear_el(c, r, e, rj.and_l(x, Sr.rr.clear(t, r, 2n+e), h))
      +ht = rj.clear(t, r, e, rj.and_r(x, Sr.rr.clear(t, r, 2n+e), h))
      %Equal.sym(Bool, y, True{}, hx) : {Bool.and(_, Sr.rr.clear(t, 1n+r, 1n+e)) == True{} : Bool}
      ht

# The jump
# --------

# no rounds jumped
def rj.none(+f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat) -> {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 0n), DocSearch.ds_rounds(Nat.sub(f, 0n), cs, Nat.add(r, 0n), Nat.sub(b, 0n))) : List<&2, Nat>}:
  %rj.sub0(f) : {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 0n), DocSearch.ds_rounds(_, cs, Nat.add(r, 0n), Nat.sub(b, 0n))) : List<&2, Nat>}
  %rj.add0(r) : {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 0n), DocSearch.ds_rounds(f, cs, _, Nat.sub(b, 0n))) : List<&2, Nat>}
  %rj.sub0(b) : {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 0n), DocSearch.ds_rounds(f, cs, r, _)) : List<&2, Nat>}
  %rj.block0(cs, r) : {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(_, DocSearch.ds_rounds(f, cs, r, b)) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, DocSearch.ds_plus(Sr.rr.zeros(cs), DocSearch.ds_rounds(f, cs, r, b)), DocSearch.ds_rounds(f, cs, r, b), rj.zero_rounds(f, cs, r, b))

# one full round, then d more as e says
def rj.step(+d: Nat, +f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat, ha: {Nat.is_le(Sr.rr.act(cs, r), b) == True{} : Bool}, e: {DocSearch.ds_rounds(f, cs, 1n+r, Nat.sub(b, Sr.rr.act(cs, r))) == DocSearch.ds_plus(Sr.rr.block(cs, 1n+r, d), DocSearch.ds_rounds(Nat.sub(f, d), cs, Nat.add(1n+r, d), Nat.sub(Nat.sub(b, Sr.rr.act(cs, r)), Nat.mul(d, Sr.rr.act(cs, r))))) : List<&2, Nat>}) -> {DocSearch.ds_rounds(1n+f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 1n+d), DocSearch.ds_rounds(Nat.sub(1n+f, 1n+d), cs, Nat.add(r, 1n+d), Nat.sub(b, Nat.mul(1n+d, Sr.rr.act(cs, r))))) : List<&2, Nat>}:
  +a = Sr.rr.act(cs, r)
  +i = rj.ind(cs, r)
  +b1 = Sr.rr.block(cs, 1n+r, d)
  +x = DocSearch.ds_rounds(Nat.sub(f, d), cs, Nat.add(1n+r, d), Nat.sub(Nat.sub(b, a), Nat.mul(d, a)))
  +rhs = DocSearch.ds_plus(Sr.rr.block(cs, r, 1n+d), DocSearch.ds_rounds(Nat.sub(f, d), cs, Nat.add(r, 1n+d), Nat.sub(b, Nat.add(a, Nat.mul(d, a)))))
  %rj.full(cs, r, b, ha) : {DocSearch.ds_plus(_, DocSearch.ds_rounds(f, cs, 1n+r, Nat.sub(b, DocSearch.ds_sum(_)))) == rhs : List<&2, Nat>}
  %rj.sum_ind(cs, r) : {DocSearch.ds_plus(i, DocSearch.ds_rounds(f, cs, 1n+r, Nat.sub(b, _))) == rhs : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, DocSearch.ds_rounds(f, cs, 1n+r, Nat.sub(b, a)), DocSearch.ds_plus(b1, x), e) : {DocSearch.ds_plus(i, _) == rhs : List<&2, Nat>}
  %rj.plus_assoc(i, b1, x) : {_ == rhs : List<&2, Nat>}
  %rj.block_step(cs, r, d) : {DocSearch.ds_plus(DocSearch.ds_plus(i, b1), x) == DocSearch.ds_plus(_, DocSearch.ds_rounds(Nat.sub(f, d), cs, Nat.add(r, 1n+d), Nat.sub(b, Nat.add(a, Nat.mul(d, a))))) : List<&2, Nat>}
  %rj.add_succ(r, d) : {DocSearch.ds_plus(DocSearch.ds_plus(i, b1), x) == DocSearch.ds_plus(DocSearch.ds_plus(i, b1), DocSearch.ds_rounds(Nat.sub(f, d), cs, _, Nat.sub(b, Nat.add(a, Nat.mul(d, a))))) : List<&2, Nat>}
  %rj.subsub(b, a, Nat.mul(d, a)) : {DocSearch.ds_plus(DocSearch.ds_plus(i, b1), x) == DocSearch.ds_plus(DocSearch.ds_plus(i, b1), DocSearch.ds_rounds(Nat.sub(f, d), cs, 1n+Nat.add(r, d), _)) : List<&2, Nat>}
  {==}

# a count that equals another moves through a hypothesis
def rj.le_tr(-n: Nat, -m: Nat, -x: Nat, -y: Nat, eq: {y == x : Nat}, h: {Nat.is_le(Nat.mul(n, y), m) == True{} : Bool}) -> {Nat.is_le(Nat.mul(n, x), m) == True{} : Bool}:
  %eq : {Nat.is_le(Nat.mul(n, _), m) == True{} : Bool}
  h

def rj.e_tr(-g: Nat, -cs: List<&2, Nat>, -r: Nat, -b: Nat, -a: Nat, -d: Nat, -x: Nat, -y: Nat, eq: {x == y : Nat}, h: {DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(b, a)) == DocSearch.ds_plus(Sr.rr.block(cs, 1n+r, d), DocSearch.ds_rounds(Nat.sub(g, d), cs, Nat.add(1n+r, d), Nat.sub(Nat.sub(b, a), Nat.mul(d, x)))) : List<&2, Nat>}) -> {DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(b, a)) == DocSearch.ds_plus(Sr.rr.block(cs, 1n+r, d), DocSearch.ds_rounds(Nat.sub(g, d), cs, Nat.add(1n+r, d), Nat.sub(Nat.sub(b, a), Nat.mul(d, y)))) : List<&2, Nat>}:
  %eq : {DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(b, a)) == DocSearch.ds_plus(Sr.rr.block(cs, 1n+r, d), DocSearch.ds_rounds(Nat.sub(g, d), cs, Nat.add(1n+r, d), Nat.sub(Nat.sub(b, a), Nat.mul(d, _)))) : List<&2, Nat>}
  h

# d full rounds at once: the d rounds are left to run (d <= f), the budget
# pays for them (d * act <= b), and no file's count ends inside them
def rj.jump(d: Nat, f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat, hd: {Nat.is_le(d, f) == True{} : Bool}, +hm: {Nat.is_le(Nat.mul(d, Sr.rr.act(cs, r)), b) == True{} : Bool}, +hc: {Sr.rr.clear(cs, r, d) == True{} : Bool}) -> {DocSearch.ds_rounds(f, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, d), DocSearch.ds_rounds(Nat.sub(f, d), cs, Nat.add(r, d), Nat.sub(b, Nat.mul(d, Sr.rr.act(cs, r))))) : List<&2, Nat>}:
  match d f:
    case 0n f:
      rj.none(f, cs, r, b)
    case 1n+p 0n:
      rj.ft({DocSearch.ds_rounds(0n, cs, r, b) == DocSearch.ds_plus(Sr.rr.block(cs, r, 1n+p), DocSearch.ds_rounds(0n, cs, Nat.add(r, 1n+p), Nat.sub(b, Nat.mul(1n+p, Sr.rr.act(cs, r))))) : List<&2, Nat>}, hd)
    case 1n 1n++g:
      +a = Sr.rr.act(cs, r)
      rj.step(0n, g, cs, r, b, rj.le_add(a, 0n, b, hm), rj.none(g, cs, 1n+r, Nat.sub(b, a)))
    case 2n++q 1n++g:
      +a = Sr.rr.act(cs, r)
      +ha = rj.le_add(a, Nat.mul(1n+q, a), b, hm)
      +hm2 = rj.le_sub(a, Nat.mul(1n+q, a), b, hm)
      +eq = rj.act(cs, r, q, hc)
      +x = Sr.rr.act(cs, 1n+r)
      +hm3 = rj.le_tr(1n+q, Nat.sub(b, a), x, a, Equal.sym(Nat, x, a, eq), hm2)
      +ih = rj.jump(1n+q, g, cs, 1n+r, Nat.sub(b, a), hd, hm3, rj.clear(cs, r, q, hc))
      rj.step(1n+q, g, cs, r, b, ha, rj.e_tr(g, cs, r, b, a, 1n+q, x, a, eq, ih))
