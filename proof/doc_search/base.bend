# eukhe: lemmas the proofs of area doc_search share

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ../../laws/wire.bend as Wire

def documents.ps.MD(m: Maybe<&2, Nat>, t: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      t

def documents.ps.none_some(-A: Type, -c: Nat, e: {None{} == Some{c} : Maybe<&2, Nat>}) -> A:
  %e : documents.ps.MD(_, A)
  Unit{}

def ps.some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{a}, Some{b}, e)

# Pages
# -----

def ps.take_drop(xs: List<&2, Nat>, k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, xs, k), List.drop(&2, Nat, xs, k)) == xs : List<&2, Nat>}:
  match xs k:
    case Nil{} k:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      %ps.take_drop(t, p) : {h <> List.append(&2, Nat, List.take(&2, Nat, t, p), List.drop(&2, Nat, t, p)) == h <> _ : List<&2, Nat>}
      {==}

def ps.drop_drop(xs: List<&2, Nat>, s: Nat, +k: Nat) -> {List.drop(&2, Nat, List.drop(&2, Nat, xs, s), k) == List.drop(&2, Nat, xs, Nat.add(s, k)) : List<&2, Nat>}:
  match xs s:
    case Nil{} s:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      ps.drop_drop(t, p, k)

def ps.put_c(after: List<&2, Nat>, -c0: Nat, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {c0 == c : Nat}:
  match after:
    case Nil{}:
      documents.ps.none_some({c0 == c : Nat}, c, h)
    case x <> t:
      ps.some_inj(c0, c, h)

# the continuation is S + K
def ps.next_c(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {Nat.add(s, k) == c : Nat}:
  match k:
    case 0n:
      documents.ps.none_some({Nat.add(s, 0n) == c : Nat}, c, h)
    case 1n+j:
      ps.put_c(List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), Nat.add(s, 1n+j), c, h)

# the page at S + K and what follows it are the list after S
def ps.contig(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, Nat.add(s, k), k), List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  +d = List.drop(&2, Nat, ps, Nat.add(s, k))
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, d, k), List.drop(&2, Nat, d, k)), d, ps.take_drop(d, k)) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  %ps.drop_drop(ps, s, k) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  ps.take_drop(List.drop(&2, Nat, ps, s), k)

# Nat order and Bool
# ------------------

def ds.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# False is not True: anything follows
def ds.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ds.BF(_, A)
  Unit{}

def ds.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ds.ft({False{} == True{} : Bool}, e)

def ds.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ds.ft({b == True{} : Bool}, e)

def ds.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ds.ft({Bool.and(False{}, b) == True{} : Bool}, ea)

def ds.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ds.le_refl(p)

def ds.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b 0n:
      {==}
    case 0n b 1n+r:
      {==}
    case 1n+p 0n c:
      ds.ft({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      ds.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      ds.le_trans(p, q, r, ab, bc)

def ds.min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ds.min_le_l(p, q)

def ds.min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ds.min_le_r(p, q)

# x below both is below their min
def ds.le_min(x: Nat, a: Nat, b: Nat, ha: {Nat.is_le(x, a) == True{} : Bool}, hb: {Nat.is_le(x, b) == True{} : Bool}) -> {Nat.is_le(x, Nat.min(a, b)) == True{} : Bool}:
  match x a b:
    case 0n 0n b:
      {==}
    case 0n 1n+p 0n:
      {==}
    case 0n 1n+p 1n+q:
      {==}
    case 1n+y 0n b:
      ds.ft({Nat.is_le(1n+y, Nat.min(0n, b)) == True{} : Bool}, ha)
    case 1n+y 1n+p 0n:
      ds.ft({Nat.is_le(1n+y, Nat.min(1n+p, 0n)) == True{} : Bool}, hb)
    case 1n+y 1n+p 1n+q:
      ds.le_min(y, p, q, ha, hb)

# a <= b: a + (b - a) is b
def ds.add_sub(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ds.ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.sub(q, p)), q, ds.add_sub(p, q, h))

def ds.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, ds.add_zero(p))

def ds.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ds.add_succ(p, b))

def ds.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), ds.add_assoc(p, b, c))

def ds.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ds.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ds.or_true_r(u: Bool) -> {Bool.or(u, True{}) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def ds.or_false_r(u: Bool) -> {Bool.or(u, False{}) == u : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# a <= b: a < 1 + b
def ds.le_lt_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      ds.ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ds.le_lt_succ(p, q, h)

def ds.le_max_l(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      ds.le_zero(b)
    case 1n+p 0n:
      ds.le_refl(p)
    case 1n+p 1n+q:
      ds.le_max_l(p, q)

def ds.le_max_r(a: Nat, b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      ds.le_refl(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ds.le_max_r(p, q)

# both below x: their max is below x
def ds.max_le(a: Nat, b: Nat, x: Nat, ha: {Nat.is_le(a, x) == True{} : Bool}, hb: {Nat.is_le(b, x) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), x) == True{} : Bool}:
  match a b x:
    case 0n b x:
      hb
    case 1n+p 0n x:
      ha
    case 1n+p 1n+q 0n:
      ds.ft({Nat.is_le(Nat.max(1n+p, 1n+q), 0n) == True{} : Bool}, ha)
    case 1n+p 1n+q 1n+y:
      ds.max_le(p, q, y, ha, hb)

# min(t, c) <= x: t <= x or c <= x
def ds.min_le_or(t: Nat, c: Nat, x: Nat, h: {Nat.is_le(Nat.min(t, c), x) == True{} : Bool}) -> {Bool.or(Nat.is_le(t, x), Nat.is_le(c, x)) == True{} : Bool}:
  match t c x:
    case 0n c 0n:
      {==}
    case 0n c 1n+y:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+y:
      ds.or_true_r(Nat.is_le(p, y))
    case 1n+p 1n+q 0n:
      ds.ft({Bool.or(Nat.is_le(1n+p, 0n), Nat.is_le(1n+q, 0n)) == True{} : Bool}, h)
    case 1n+p 1n+q 1n+y:
      ds.min_le_or(p, q, y, h)

# a + (b + c) is b + (a + c)
def ds.add_swap(a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), ds.add_swap(p, b, c)), Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), ds.add_succ(b, Nat.add(p, c))))

# (a - b) - c is a - (b + c)
def ds.sub_sub(a: Nat, b: Nat, +c: Nat) -> {Nat.sub(Nat.sub(a, b), c) == Nat.sub(a, Nat.add(b, c)) : Nat}:
  match a b:
    case 0n b:
      match c:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ds.sub_sub(p, q, c)

# The rules exactly
# -----------------

# the code's sum is the spec's
def ds.sum(xs: List<&2, Nat>) -> {Sr.sum(xs) == DocSearch.ds_sum(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %ds.sum(t) : {Nat.add(x, Sr.sum(t)) == Nat.add(x, _) : Nat}
      {==}

# Fetch
# -----

def ds.or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ds.ft({Bool.or(False{}, b) == True{} : Bool}, e)

# y <= z, and z <= x or b: y <= x or b
def ds.or_le(+y: Nat, +z: Nat, +x: Nat, b: Bool, yz: {Nat.is_le(y, z) == True{} : Bool}, h: {Bool.or(Nat.is_le(z, x), b) == True{} : Bool}) -> {Bool.or(Nat.is_le(y, x), b) == True{} : Bool}:
  match b:
    case True{}:
      ds.or_true_r(Nat.is_le(y, x))
    case False{}:
      +hz = Equal.trans(Bool, Nat.is_le(z, x), Bool.or(Nat.is_le(z, x), False{}), True{}, Equal.sym(Bool, Bool.or(Nat.is_le(z, x), False{}), Nat.is_le(z, x), ds.or_false_r(Nat.is_le(z, x))), h)
      Equal.trans(Bool, Bool.or(Nat.is_le(y, x), False{}), Nat.is_le(y, x), True{}, ds.or_false_r(Nat.is_le(y, x)), ds.le_trans(y, z, x, yz, hz))

# a <= x or c, and b <= x or c: max(a, b) <= x or c
def ds.or_max(+a: Nat, +b: Nat, +x: Nat, c: Bool, ha: {Bool.or(Nat.is_le(a, x), c) == True{} : Bool}, hb: {Bool.or(Nat.is_le(b, x), c) == True{} : Bool}) -> {Bool.or(Nat.is_le(Nat.max(a, b), x), c) == True{} : Bool}:
  match c:
    case True{}:
      ds.or_true_r(Nat.is_le(Nat.max(a, b), x))
    case False{}:
      +ea = Equal.trans(Bool, Nat.is_le(a, x), Bool.or(Nat.is_le(a, x), False{}), True{}, Equal.sym(Bool, Bool.or(Nat.is_le(a, x), False{}), Nat.is_le(a, x), ds.or_false_r(Nat.is_le(a, x))), ha)
      +eb = Equal.trans(Bool, Nat.is_le(b, x), Bool.or(Nat.is_le(b, x), False{}), True{}, Equal.sym(Bool, Bool.or(Nat.is_le(b, x), False{}), Nat.is_le(b, x), ds.or_false_r(Nat.is_le(b, x))), hb)
      Equal.trans(Bool, Bool.or(Nat.is_le(Nat.max(a, b), x), False{}), Nat.is_le(Nat.max(a, b), x), True{}, ds.or_false_r(Nat.is_le(Nat.max(a, b), x)), ds.max_le(a, b, x, ea, eb))

# t <= x or c <= x: min(t, c) <= x
def ds.or_min_le(t: Nat, c: Nat, x: Nat, h: {Bool.or(Nat.is_le(t, x), Nat.is_le(c, x)) == True{} : Bool}) -> {Nat.is_le(Nat.min(t, c), x) == True{} : Bool}:
  match t c x:
    case 0n c x:
      ds.le_zero(x)
    case 1n+p 0n x:
      ds.le_zero(x)
    case 1n+p 1n+q 0n:
      ds.ft({Nat.is_le(Nat.min(1n+p, 1n+q), 0n) == True{} : Bool}, h)
    case 1n+p 1n+q 1n+y:
      ds.or_min_le(p, q, y, h)

# the spec's needed line of a range is the code's reach
def ds.need_reach(r: Sr.Range, +base: Nat, +x: Nat, b: Bool, h: {Bool.or(Nat.is_le(DocSearch.ds_need(r, base), x), b) == True{} : Bool}) -> {Bool.or(Nat.is_le(Sr.reach(r, base), x), b) == True{} : Bool}:
  match r:
    case Sr.Range{a, z}:
      match z:
        case None{}:
          h
        case Some{e}:
          h

def ds.reach_need(r: Sr.Range, +base: Nat, +x: Nat, b: Bool, h: {Bool.or(Nat.is_le(Sr.reach(r, base), x), b) == True{} : Bool}) -> {Bool.or(Nat.is_le(DocSearch.ds_need(r, base), x), b) == True{} : Bool}:
  match r:
    case Sr.Range{a, z}:
      match z:
        case None{}:
          h
        case Some{e}:
          h

# a fetch of x past the last line the ranges need, or past maxb, covers
# every range
def ds.covers_or(rs: List<&2, Sr.Range>, +x: Nat, +base: Nat, +maxb: Nat, +h: {Bool.or(Nat.is_le(Sr.reach.top(rs, base), x), Nat.is_le(1n+maxb, x)) == True{} : Bool}) -> {DocSearch.ds_covers(rs, x, base, maxb) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      +h1 = ds.or_le(Sr.reach(r, base), Nat.max(Sr.reach(r, base), Sr.reach.top(t, base)), x, Nat.is_le(1n+maxb, x), ds.le_max_l(Sr.reach(r, base), Sr.reach.top(t, base)), h)
      +h2 = ds.or_le(Sr.reach.top(t, base), Nat.max(Sr.reach(r, base), Sr.reach.top(t, base)), x, Nat.is_le(1n+maxb, x), ds.le_max_r(Sr.reach(r, base), Sr.reach.top(t, base)), h)
      ds.and_t(Bool.or(Nat.is_le(DocSearch.ds_need(r, base), x), Nat.is_le(1n+maxb, x)), DocSearch.ds_covers(t, x, base, maxb), ds.reach_need(r, base, x, Nat.is_le(1n+maxb, x), h1), ds.covers_or(t, x, base, maxb, h2))

# a fetch of x that covers every range is past the last line they need,
# or past maxb
def ds.top_or(rs: List<&2, Sr.Range>, +x: Nat, +base: Nat, +maxb: Nat, +h: {DocSearch.ds_covers(rs, x, base, maxb) == True{} : Bool}) -> {Bool.or(Nat.is_le(Sr.reach.top(rs, base), x), Nat.is_le(1n+maxb, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      ds.or_l(Nat.is_le(0n, x), Nat.is_le(1n+maxb, x), ds.le_zero(x))
    case +r <> +t:
      +ha = ds.and_l(Bool.or(Nat.is_le(DocSearch.ds_need(r, base), x), Nat.is_le(1n+maxb, x)), DocSearch.ds_covers(t, x, base, maxb), h)
      +hb = ds.and_r(Bool.or(Nat.is_le(DocSearch.ds_need(r, base), x), Nat.is_le(1n+maxb, x)), DocSearch.ds_covers(t, x, base, maxb), h)
      ds.or_max(Sr.reach(r, base), Sr.reach.top(t, base), x, Nat.is_le(1n+maxb, x), ds.need_reach(r, base, x, Nat.is_le(1n+maxb, x), ha), ds.top_or(t, x, base, maxb, hb))

# The entry
# ---------

def dsb.BD(b: Bool, A: Type, B: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      B

# True is not False: anything follows
def dsb.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : dsb.BD(_, Unit, A)
  Unit{}

# a list that fits reads back whole (laws/wire.bend wire_list_round_trip,
# turned around to rewrite a decoded spelling into its list)
def dsb.read(+xs: List<&2, Nat>, h: {DocSearch.ds_fits(xs) == True{} : Bool}) -> {Wr.Got{xs, ""} == Wr.get_list(~Nat, ~Wr.get_nat, DocSearch.ds_spell(xs)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")), Wr.Got{xs, ""}, Wire.wire_list_round_trip(xs, "", h))

def dsb.bitn(b: Bool) -> {FDs.bitn(b) == DocSearch.ds_bit(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dsb.maybn(m: Maybe<&2, Nat>) -> {FDs.maybn(m) == DocSearch.ds_opt(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def dsb.bit_of(b: Bool) -> {Some{b} == FDs.bit(DocSearch.ds_bit(b)) : Maybe<&2, Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dsb.why(w: Sr.Reason) -> {FDs.why.n(w) == DocSearch.ds_why(w) : Nat}:
  match w:
    case Sr.Binary{}:
      {==}
    case Sr.Unreadable{}:
      {==}
    case Sr.Excluded{}:
      {==}
    case Sr.Link{}:
      {==}
    case Sr.Broken{}:
      {==}

def dsb.cls(c: Sr.Class) -> {FDs.cls.n(c) == DocSearch.ds_class(c) : Nat}:
  match c:
    case Sr.NoMatch{}:
      {==}
    case Sr.Shown{}:
      {==}
    case Sr.PagedOut{}:
      {==}
    case Sr.Unsearched{}:
      {==}
    case Sr.Skipped{w}:
      %dsb.why(w) : {4n+FDs.why.n(w) == 4n+_ : Nat}
      {==}

# the reply to what a file held is the spec's
def dsb.said(o: Sr.Out, +k: Nat) -> {FDs.step.met.nats(o, k) == DocSearch.ds_said(o, k) : List<&2, Nat>}:
  match o:
    case Sr.Out{i, +c, +cut, +pa}:
      %dsb.cls(c) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [_, DocSearch.ds_bit(cut), DocSearch.ds_bit(pa), k] : List<&2, Nat>}
      %dsb.bitn(cut) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [FDs.cls.n(c), _, DocSearch.ds_bit(pa), k] : List<&2, Nat>}
      %dsb.bitn(pa) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [FDs.cls.n(c), FDs.bitn(cut), _, k] : List<&2, Nat>}
      {==}

# the event a spelled file reads as
def dsb.met(f: Sr.Form) -> {Some{FDs.Met{f}} == FDs.ev(DocSearch.ds_met(f)) : Maybe<&2, FDs.Ev>}:
  match f:
    case Sr.Opened{h, big}:
      match big:
        case True{}:
          {==}
        case False{}:
          {==}
    case Sr.Skip{w}:
      match w:
        case Sr.Binary{}:
          {==}
        case Sr.Unreadable{}:
          {==}
        case Sr.Excluded{}:
          {==}
        case Sr.Link{}:
          {==}
        case Sr.Broken{}:
          {==}

# the ranges a spelled ask reads as
def dsb.ranges(rs: List<&2, Sr.Range>) -> {Some{rs} == FDs.ranges(DocSearch.ds_bounds(rs)) : Maybe<&2, List<&2, Sr.Range>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Sr.Range{+a, z}:
          match z:
            case None{}:
              %dsb.ranges(t) : {Some{Sr.Range{a, None{}} <> t} == FDs.ranges.cons(Sr.Range{a, None{}}, _) : Maybe<&2, List<&2, Sr.Range>>}
              {==}
            case Some{+e}:
              %dsb.ranges(t) : {Some{Sr.Range{a, Some{e}} <> t} == FDs.ranges.cons(Sr.Range{a, Some{e}}, _) : Maybe<&2, List<&2, Sr.Range>>}
              {==}

# Refusals
# --------

# a or False is False only when a is
def dsb.or_f(a: Bool, e: {Bool.or(a, False{}) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# a Nat over 1 is no Bool
def dsb.bit_none(n: Nat, e: {Nat.is_le(n, 1n) == False{} : Bool}) -> {None{} == FDs.bit(n) : Maybe<&2, Bool>}:
  match n:
    case 0n:
      dsb.tf({None{} == FDs.bit(0n) : Maybe<&2, Bool>}, e)
    case 1n:
      dsb.tf({None{} == FDs.bit(1n) : Maybe<&2, Bool>}, e)
    case 2n+x:
      {==}

# pairs of an odd count read as no ranges
def dsb.ranges_none(xs: List<&2, Nat>, e: {DocSearch.ds_pairs_ok(xs) == False{} : Bool}) -> {None{} == FDs.ranges(xs) : Maybe<&2, List<&2, Sr.Range>>}:
  match xs:
    case Nil{}:
      dsb.tf({None{} == FDs.ranges(Nil{}) : Maybe<&2, List<&2, Sr.Range>>}, e)
    case a <> t:
      match t:
        case Nil{}:
          {==}
        case +z <> u:
          %dsb.ranges_none(u, e) : {None{} == FDs.ranges.cons(Sr.Range{a, FDs.stop(z)}, _) : Maybe<&2, List<&2, Sr.Range>>}
          {==}
