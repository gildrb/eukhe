# proof_quirks: the quirks rulebook laws of S6, about bend/infer.bend.
#
# Compile: an unknown directive fails known_all (`pq.ka_app`); a clash
# makes the rulebook ambiguous (`pq.amb_app`); a swap of two neighbours
# changes neither known_all (`pq.ka_swap`) nor ambiguous (`pq.amb_swap`,
# clash is symmetric).
# Lookup: with no rule that applies the scan keeps None (`pq.none_go`);
# once a rule applies the best stays Some (`pq.stay_k`). Two rules that
# both apply and do not clash give the same best in either order
# (`pq.better_swap`: at one rank they agree on the value). In a rulebook
# that compiles, before r the best is below r's rank or equal to r
# (`pq.pre_ok`), and from r on it is r's rank and value (`pq.good`).
# The thinking ladder: the chosen ladder is a plain case split
# (reflexivity). A level is in the offer of a map exactly when the map
# keeps it (`pq.lad_has_keep`, from the S10 filter lemmas), and the filled
# map keeps a level exactly when the ladder rule does (`pq.lad_fill_keep`).
# With the shipped default ladders the ladder rule keeps what the S10
# rule keeps (`pq.lad_ship_e`), so the offers agree (`pq.lad_offer_fill`,
# by induction on the list).

import Base
import ./infer.bend as If
import ./effort.bend as Ef
import ./proof_effort.bend as Pe

# Logic
# -----

def pq.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pq.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pq.BD(_, Unit, A)
  Unit{}

def pq.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pq.BD(_, A, Unit)
  Unit{}

def pq.flip(-A: Type, -a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> A:
  pq.absurd(A, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

def pq.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pq.absurdF({False{} == True{} : Bool}, h)

def pq.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pq.absurdF({b == True{} : Bool}, h)

def pq.and_t(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pq.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the right side of a false and whose left side holds
def pq.and_tf(a: Bool, -b: Bool, h: {Bool.and(a, b) == False{} : Bool}, ha: {a == True{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pq.absurdF({b == False{} : Bool}, ha)

def pq.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pq.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pq.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pq.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pq.or_tl(-a: Bool, -b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def pq.or_tr(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# the right side of a true or whose left side fails
def pq.or_fl(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, na: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      pq.absurd({b == True{} : Bool}, na)
    case False{}:
      h

def pq.or_and_f(c: Bool, -y: Bool, -z: Bool, h: {Bool.or(Bool.and(c, y), z) == True{} : Bool}, nc: {c == False{} : Bool}) -> {z == True{} : Bool}:
  match c:
    case True{}:
      pq.absurd({z == True{} : Bool}, nc)
    case False{}:
      h

def pq.not_f(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pq.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pq.and_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pq.or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pq.or4(c: Bool, +x: Bool, +y: Bool, +z: Bool) -> {Bool.or(Bool.or(c, x), Bool.or(y, z)) == Bool.or(Bool.or(c, y), Bool.or(x, z)) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pq.or_swap(x, y, z)

# x, y hold and and(x, and(y, not z)) fails: z holds
def pq.ncv(x: Bool, y: Bool, z: Bool, nc: {Bool.and(x, Bool.and(y, Bool.not(z))) == False{} : Bool}, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {z == True{} : Bool}:
  match x y z:
    case False{} _ _:
      pq.absurdF({z == True{} : Bool}, hx)
    case True{} False{} _:
      pq.absurdF({z == True{} : Bool}, hy)
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      pq.absurd({False{} == True{} : Bool}, nc)

# Numbers
# -------

def pq.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pq.eq_refl(p)

def pq.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pq.eq_true(p, q, h))

def pq.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pq.eq_comm(p, q)

def pq.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %ab : {Nat.is_eq(a, _) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pq.eq_refl(a))

def pq.eq_tr(+x: Nat, +y: Nat, +z: Nat, xz: {Nat.is_eq(x, z) == True{} : Bool}, yz: {Nat.is_eq(y, z) == True{} : Bool}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  %Equal.sym(Nat, y, z, pq.eq_true(y, z, yz)) : {Nat.is_eq(x, _) == True{} : Bool}
  xz

def pq.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pq.lt_irrefl(p)

def pq.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      pq.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      pq.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pq.lt_trans(p, q, r, ab, bc)

# neither below the other: equal
def pq.tri(x: Nat, y: Nat, n1: {Nat.is_lt(y, x) == False{} : Bool}, n2: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pq.absurd({Nat.is_eq(0n, 1n+q) == True{} : Bool}, n2)
    case 1n+p 0n:
      pq.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool}, n1)
    case 1n+p 1n+q:
      pq.tri(p, q, n1, n2)

def pq.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pq.lt_le(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, pq.le0(q))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pq.lt_le(p, q)

def pq.lt_at(-k: Nat, -x: Nat, -y: Nat, e: {k == x : Nat}, h: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_lt(k, y) == False{} : Bool}:
  %Equal.sym(Nat, k, x, e) : {Nat.is_lt(_, y) == False{} : Bool}
  h

# k below x and not below y: x is not below y
def pq.lt_gap(+k: Nat, +x: Nat, +y: Nat, c: Bool, ec: {Nat.is_lt(x, y) == c : Bool}, kx: {Nat.is_lt(k, x) == True{} : Bool}, ky: {Nat.is_lt(k, y) == False{} : Bool}) -> {Nat.is_lt(x, y) == False{} : Bool}:
  match c:
    case True{}:
      pq.flip({Nat.is_lt(x, y) == False{} : Bool}, Nat.is_lt(k, y), pq.lt_trans(k, x, y, kx, ec), ky)
    case False{}:
      ec

# Compiling
# ---------

def pq.ka_app(pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +known: List<&2, Nat>, bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}) -> {If.known_all(List.append(&2, If.Rule, pre, r <> post), known) == False{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, If.elem(known, If.Rule.dir(r)), False{}, bad) : {Bool.and(_, If.known_all(post, known)) == False{} : Bool}
      {==}
    case +h <> +t:
      %Equal.sym(Bool, If.known_all(List.append(&2, If.Rule, t, r <> post), known), False{}, pq.ka_app(t, r, post, known, bad)) : {Bool.and(If.elem(known, If.Rule.dir(h)), _) == False{} : Bool}
      pq.and_f(If.elem(known, If.Rule.dir(h)))

def pq.quirk_unknown_rejected(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}) -> {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}:
  %Equal.sym(Bool, If.known_all(List.append(&2, If.Rule, pre, r <> post), known), False{}, pq.ka_app(pre, r, post, known, bad)) : {Bool.and(_, Bool.not(If.ambiguous(List.append(&2, If.Rule, pre, r <> post)))) == False{} : Bool}
  {==}

def pq.clashes_app(+a: If.Rule, mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.clashes(a, List.append(&2, If.Rule, mid, b <> post)) == True{} : Bool}:
  match mid:
    case Nil{}:
      pq.or_tl(If.clash(a, b), If.clashes(a, post), both)
    case +s <> +t:
      pq.or_tr(If.clash(a, s), If.clashes(a, List.append(&2, If.Rule, t, b <> post)), pq.clashes_app(a, t, b, post, both))

def pq.amb_app(pre: List<&2, If.Rule>, +a: If.Rule, +mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.ambiguous(List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == True{} : Bool}:
  match pre:
    case Nil{}:
      +X = List.append(&2, If.Rule, mid, b <> post)
      pq.or_tl(If.clashes(a, X), If.ambiguous(X), pq.clashes_app(a, mid, b, post, both))
    case +h <> +t:
      +X = List.append(&2, If.Rule, t, a <> List.append(&2, If.Rule, mid, b <> post))
      pq.or_tr(If.clashes(h, X), If.ambiguous(X), pq.amb_app(t, a, mid, b, post, both))

def pq.quirk_clash_rejected(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.compiles(known, List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == False{} : Bool}:
  +L = List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))
  %Equal.sym(Bool, If.ambiguous(L), True{}, pq.amb_app(pre, a, mid, b, post, both)) : {Bool.and(If.known_all(L, known), Bool.not(_)) == False{} : Bool}
  pq.and_f(If.known_all(L, known))

def pq.ka_swap(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +known: List<&2, Nat>) -> {If.known_all(List.append(&2, If.Rule, pre, b <> a <> post), known) == If.known_all(List.append(&2, If.Rule, pre, a <> b <> post), known) : Bool}:
  match pre:
    case Nil{}:
      pq.and_swap(If.elem(known, If.Rule.dir(b)), If.elem(known, If.Rule.dir(a)), If.known_all(post, known))
    case +h <> +t:
      %pq.ka_swap(t, a, b, post, known) : {Bool.and(If.elem(known, If.Rule.dir(h)), If.known_all(List.append(&2, If.Rule, t, b <> a <> post), known)) == Bool.and(If.elem(known, If.Rule.dir(h)), _) : Bool}
      {==}

def pq.cl_app_swap(+s: If.Rule, pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.clashes(s, List.append(&2, If.Rule, pre, b <> a <> post)) == If.clashes(s, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  match pre:
    case Nil{}:
      pq.or_swap(If.clash(s, b), If.clash(s, a), If.clashes(s, post))
    case +h <> +t:
      %pq.cl_app_swap(s, t, a, b, post) : {Bool.or(If.clash(s, h), If.clashes(s, List.append(&2, If.Rule, t, b <> a <> post))) == Bool.or(If.clash(s, h), _) : Bool}
      {==}

def pq.clash_sym(a: If.Rule, b: If.Rule) -> {If.clash(a, b) == If.clash(b, a) : Bool}:
  match a b:
    case If.Rule{+la, +ta, +da, +va} If.Rule{+lb, +tb, +db, +vb}:
      +ka = If.Lay.rank(la)
      +kb = If.Lay.rank(lb)
      +C = If.clash(If.Rule{la, ta, da, va}, If.Rule{lb, tb, db, vb})
      %pq.eq_comm(ka, kb) : {C == Bool.and(_, Bool.and(Nat.is_eq(tb, ta), Bool.and(Nat.is_eq(db, da), Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(ta, tb) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(_, Bool.and(Nat.is_eq(db, da), Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(da, db) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(Nat.is_eq(ta, tb), Bool.and(_, Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(va, vb) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(_)))) : Bool}
      {==}

def pq.amb_swap(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.ambiguous(List.append(&2, If.Rule, pre, b <> a <> post)) == If.ambiguous(List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  match pre:
    case Nil{}:
      %pq.clash_sym(a, b) : {Bool.or(Bool.or(_, If.clashes(b, post)), Bool.or(If.clashes(a, post), If.ambiguous(post))) == Bool.or(Bool.or(If.clash(a, b), If.clashes(a, post)), Bool.or(If.clashes(b, post), If.ambiguous(post))) : Bool}
      pq.or4(If.clash(a, b), If.clashes(b, post), If.clashes(a, post), If.ambiguous(post))
    case +h <> +t:
      +X1 = List.append(&2, If.Rule, t, b <> a <> post)
      +X2 = List.append(&2, If.Rule, t, a <> b <> post)
      %pq.cl_app_swap(h, t, a, b, post) : {Bool.or(If.clashes(h, X1), If.ambiguous(X1)) == Bool.or(_, If.ambiguous(X2)) : Bool}
      %pq.amb_swap(t, a, b, post) : {Bool.or(If.clashes(h, X1), If.ambiguous(X1)) == Bool.or(If.clashes(h, X1), _) : Bool}
      {==}

def pq.quirk_compile_order_free(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.compiles(known, List.append(&2, If.Rule, pre, b <> a <> post)) == If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  +L1 = List.append(&2, If.Rule, pre, b <> a <> post)
  +L2 = List.append(&2, If.Rule, pre, a <> b <> post)
  %pq.ka_swap(pre, a, b, post, known) : {Bool.and(If.known_all(L1, known), Bool.not(If.ambiguous(L1))) == Bool.and(_, Bool.not(If.ambiguous(L2))) : Bool}
  %pq.amb_swap(pre, a, b, post) : {Bool.and(If.known_all(L1, known), Bool.not(If.ambiguous(L1))) == Bool.and(If.known_all(L1, known), Bool.not(_)) : Bool}
  {==}

# Lookup: none and some
# ---------------------

def pq.none_go(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {If.look.go(rs, q, d, b, hit) == b : Maybe<&2, If.Best>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      match hit:
        case True{}:
          +H = Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d))
          +z = Nat.is_le(0n, If.Rule.rank(r))
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(rest, q, d, 0n), none), eh)
          pq.flip({If.look.go(r <> rest, q, d, b, True{}) == b : Maybe<&2, If.Best>}, z, pq.le0(If.Rule.rank(r)), le)
        case False{}:
          +H = Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(0n, If.Rule.rank(r)))
          pq.none_go(rest, q, d, b, If.use.at(rest, q, d), {==}, pq.or_r(H, If.any_at(rest, q, d, 0n), none))

def pq.quirk_unknown_when_none(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {If.lookup(rs, q, d) == If.Unknown{} : If.Ans}:
  %Equal.sym(Maybe<&2, If.Best>, If.look.go(rs, q, d, None{}, If.use.at(rs, q, d)), None{}, pq.none_go(rs, q, d, None{}, If.use.at(rs, q, d), {==}, none)) : {If.ans(_) == If.Unknown{} : If.Ans}
  {==}

def pq.better_at_k(c: Bool, x: If.Best, +r: If.Rule) -> {If.is_known(If.ans(If.better.at(c, x, r))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      match x:
        case If.Best{k, v}:
          {==}

def pq.better_k(b: Maybe<&2, If.Best>, +r: If.Rule) -> {If.is_known(If.ans(If.better(b, r))) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{+x}:
      pq.better_at_k(Nat.is_lt(If.Best.rank(x), If.Rule.rank(r)), x, r)

def pq.stay_k(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, pb: {If.is_known(If.ans(b)) == True{} : Bool}) -> {If.is_known(If.ans(If.look.go(rs, q, d, b, hit))) == True{} : Bool}:
  match rs:
    case Nil{}:
      pb
    case +r <> +rest:
      match hit:
        case True{}:
          pq.stay_k(rest, q, d, If.better(b, r), If.use.at(rest, q, d), pq.better_k(b, r))
        case False{}:
          pq.stay_k(rest, q, d, b, If.use.at(rest, q, d), pb)

def pq.found_k(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, some: {If.any_at(rs, q, d, 0n) == True{} : Bool}) -> {If.is_known(If.ans(If.look.go(rs, q, d, b, hit))) == True{} : Bool}:
  match rs:
    case Nil{}:
      pq.absurdF({If.is_known(If.ans(b)) == True{} : Bool}, some)
    case +r <> +rest:
      match hit:
        case True{}:
          pq.stay_k(rest, q, d, If.better(b, r), If.use.at(rest, q, d), pq.better_k(b, r))
        case False{}:
          +z = pq.or_and_f(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(0n, If.Rule.rank(r)), If.any_at(rest, q, d, 0n), some, eh)
          pq.found_k(rest, q, d, b, If.use.at(rest, q, d), {==}, z)

def pq.quirk_known_when_some(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, some: {If.any_at(rs, q, d, 0n) == True{} : Bool}) -> {If.is_known(If.lookup(rs, q, d)) == True{} : Bool}:
  pq.found_k(rs, q, d, None{}, If.use.at(rs, q, d), {==}, some)

# Two rules that apply
# --------------------

def pq.val_of(+ta: Nat, +tb: Nat, +da: Nat, +db: Nat, +va: Nat, +vb: Nat, +f: Nat, +d: Nat, nc: {Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb)))) == False{} : Bool}, af: {Nat.is_eq(ta, f) == True{} : Bool}, bf: {Nat.is_eq(tb, f) == True{} : Bool}, ad: {Nat.is_eq(da, d) == True{} : Bool}, bd: {Nat.is_eq(db, d) == True{} : Bool}) -> {va == vb : Nat}:
  pq.eq_true(va, vb, pq.ncv(Nat.is_eq(ta, tb), Nat.is_eq(da, db), Nat.is_eq(va, vb), nc, pq.eq_tr(ta, tb, f, af, bf), pq.eq_tr(da, db, d, ad, bd)))

# two rules of one rank that apply with one directive and do not clash
# have one value
def pq.same_val(+q: If.Query, +a: If.Rule, +b: If.Rule, +d: Nat, nc: {If.clash(a, b) == False{} : Bool}, +ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, +hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}, er: {Nat.is_eq(If.Rule.rank(a), If.Rule.rank(b)) == True{} : Bool}) -> {If.Rule.val(a) == If.Rule.val(b) : Nat}:
  match q a b:
    case If.Query{+f, m, h} If.Rule{If.Fam{}, +ta, +da, +va} If.Rule{If.Fam{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, f, d, nc, pq.and_l(Nat.is_eq(ta, f), Nat.is_eq(da, d), ha), pq.and_l(Nat.is_eq(tb, f), Nat.is_eq(db, d), hb), pq.and_r(Nat.is_eq(ta, f), Nat.is_eq(da, d), ha), pq.and_r(Nat.is_eq(tb, f), Nat.is_eq(db, d), hb))
    case If.Query{f, +m, h} If.Rule{If.Mod{}, +ta, +da, +va} If.Rule{If.Mod{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, m, d, nc, pq.and_l(Nat.is_eq(ta, m), Nat.is_eq(da, d), ha), pq.and_l(Nat.is_eq(tb, m), Nat.is_eq(db, d), hb), pq.and_r(Nat.is_eq(ta, m), Nat.is_eq(da, d), ha), pq.and_r(Nat.is_eq(tb, m), Nat.is_eq(db, d), hb))
    case If.Query{f, m, +h} If.Rule{If.Host{}, +ta, +da, +va} If.Rule{If.Host{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, h, d, nc, pq.and_l(Nat.is_eq(ta, h), Nat.is_eq(da, d), ha), pq.and_l(Nat.is_eq(tb, h), Nat.is_eq(db, d), hb), pq.and_r(Nat.is_eq(ta, h), Nat.is_eq(da, d), ha), pq.and_r(Nat.is_eq(tb, h), Nat.is_eq(db, d), hb))
    case If.Query{f, m, h} If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Host{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Host{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      pq.absurdF({va == vb : Nat}, er)

# the best of a then b is the best of b then a, from None
def pq.pair_swap(+a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, c1: Bool, +e1: {Nat.is_lt(If.Rule.rank(b), If.Rule.rank(a)) == c1 : Bool}, c2: Bool, +e2: {Nat.is_lt(If.Rule.rank(a), If.Rule.rank(b)) == c2 : Bool}, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better.at(c1, If.Best{If.Rule.rank(b), If.Rule.val(b)}, a) == If.better.at(c2, If.Best{If.Rule.rank(a), If.Rule.val(a)}, b) : Maybe<&2, If.Best>}:
  match c1 c2:
    case True{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      pq.flip({If.better.at(True{}, If.Best{RB, If.Rule.val(b)}, a) == If.better.at(True{}, If.Best{RA, If.Rule.val(a)}, b) : Maybe<&2, If.Best>}, Nat.is_lt(RA, RA), pq.lt_trans(RA, RB, RA, e2, e1), pq.lt_irrefl(RA))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VA = If.Rule.val(a)
      +VB = If.Rule.val(b)
      +er = pq.tri(RA, RB, e1, e2)
      +ev = pq.same_val(q, a, b, d, nc, ha, hb, er)
      +ek = pq.eq_true(RA, RB, er)
      %ek : {Some{If.Best{_, VB}} == Some{If.Best{RA, VA}} : Maybe<&2, If.Best>}
      %ev : {Some{If.Best{RA, _}} == Some{If.Best{RA, VA}} : Maybe<&2, If.Best>}
      {==}

# the same, from Some{Best{k, v}}
def pq.some_swap(+k: Nat, +v: Nat, +a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, ca: Bool, +ea: {Nat.is_lt(k, If.Rule.rank(a)) == ca : Bool}, cb: Bool, +eb: {Nat.is_lt(k, If.Rule.rank(b)) == cb : Bool}, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better(If.better.at(cb, If.Best{k, v}, b), a) == If.better(If.better.at(ca, If.Best{k, v}, a), b) : Maybe<&2, If.Best>}:
  match ca cb:
    case True{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      pq.pair_swap(a, b, q, d, Nat.is_lt(RB, RA), {==}, Nat.is_lt(RA, RB), {==}, nc, ha, hb)
    case True{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VA = If.Rule.val(a)
      %Equal.sym(Bool, Nat.is_lt(k, RA), True{}, ea) : {If.better.at(_, If.Best{k, v}, a) == If.better.at(Nat.is_lt(RA, RB), If.Best{RA, VA}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(RA, RB), False{}, pq.lt_gap(k, RA, RB, Nat.is_lt(RA, RB), {==}, ea, eb)) : {If.better.at(True{}, If.Best{k, v}, a) == If.better.at(_, If.Best{RA, VA}, b) : Maybe<&2, If.Best>}
      {==}
    case False{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VB = If.Rule.val(b)
      %Equal.sym(Bool, Nat.is_lt(RB, RA), False{}, pq.lt_gap(k, RB, RA, Nat.is_lt(RB, RA), {==}, eb, ea)) : {If.better.at(_, If.Best{RB, VB}, a) == If.better.at(Nat.is_lt(k, RB), If.Best{k, v}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(k, RB), True{}, eb) : {If.better.at(False{}, If.Best{RB, VB}, a) == If.better.at(_, If.Best{k, v}, b) : Maybe<&2, If.Best>}
      {==}
    case False{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      %Equal.sym(Bool, Nat.is_lt(k, RA), False{}, ea) : {If.better.at(_, If.Best{k, v}, a) == If.better.at(Nat.is_lt(k, RB), If.Best{k, v}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(k, RB), False{}, eb) : {If.better.at(False{}, If.Best{k, v}, a) == If.better.at(_, If.Best{k, v}, b) : Maybe<&2, If.Best>}
      {==}

# two rules that apply and do not clash give one best in either order
def pq.better_swap(s: Maybe<&2, If.Best>, +a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better(If.better(s, b), a) == If.better(If.better(s, a), b) : Maybe<&2, If.Best>}:
  match s:
    case None{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      pq.pair_swap(a, b, q, d, Nat.is_lt(RB, RA), {==}, Nat.is_lt(RA, RB), {==}, nc, ha, hb)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.some_swap(k, v, a, b, q, d, Nat.is_lt(k, If.Rule.rank(a)), {==}, Nat.is_lt(k, If.Rule.rank(b)), {==}, nc, ha, hb)

def pq.swap_go(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +d: Nat, +s: Maybe<&2, If.Best>, h1: Bool, h2: Bool, +e1: {If.use.at(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == h1 : Bool}, +e2: {If.use.at(List.append(&2, If.Rule, pre, a <> b <> post), q, d) == h2 : Bool}, +nc: {If.clash(a, b) == False{} : Bool}) -> {If.look.go(List.append(&2, If.Rule, pre, b <> a <> post), q, d, s, h1) == If.look.go(List.append(&2, If.Rule, pre, a <> b <> post), q, d, s, h2) : Maybe<&2, If.Best>}:
  match pre:
    case Nil{}:
      match h1 h2:
        case True{} True{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          +U = If.use.at(post, q, d)
          %Equal.sym(Bool, Ha, True{}, e2) : {If.look.go(a <> post, q, d, If.better(s, b), _) == If.look.go(b <> post, q, d, If.better(s, a), Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, True{}, e1) : {If.look.go(a <> post, q, d, If.better(s, b), True{}) == If.look.go(b <> post, q, d, If.better(s, a), _) : Maybe<&2, If.Best>}
          %pq.better_swap(s, a, b, q, d, nc, e2, e1) : {If.look.go(post, q, d, If.better(If.better(s, b), a), U) == If.look.go(post, q, d, _, U) : Maybe<&2, If.Best>}
          {==}
        case True{} False{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, False{}, e2) : {If.look.go(a <> post, q, d, If.better(s, b), _) == If.look.go(b <> post, q, d, s, Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, True{}, e1) : {If.look.go(a <> post, q, d, If.better(s, b), False{}) == If.look.go(b <> post, q, d, s, _) : Maybe<&2, If.Best>}
          {==}
        case False{} True{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, True{}, e2) : {If.look.go(a <> post, q, d, s, _) == If.look.go(b <> post, q, d, If.better(s, a), Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, False{}, e1) : {If.look.go(a <> post, q, d, s, True{}) == If.look.go(b <> post, q, d, If.better(s, a), _) : Maybe<&2, If.Best>}
          {==}
        case False{} False{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, False{}, e2) : {If.look.go(a <> post, q, d, s, _) == If.look.go(b <> post, q, d, s, Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, False{}, e1) : {If.look.go(a <> post, q, d, s, False{}) == If.look.go(b <> post, q, d, s, _) : Maybe<&2, If.Best>}
          {==}
    case +h <> +t:
      match h1 h2:
        case True{} True{}:
          pq.swap_go(t, a, b, post, q, d, If.better(s, h), If.use.at(List.append(&2, If.Rule, t, b <> a <> post), q, d), If.use.at(List.append(&2, If.Rule, t, a <> b <> post), q, d), {==}, {==}, nc)
        case False{} False{}:
          pq.swap_go(t, a, b, post, q, d, s, If.use.at(List.append(&2, If.Rule, t, b <> a <> post), q, d), If.use.at(List.append(&2, If.Rule, t, a <> b <> post), q, d), {==}, {==}, nc)
        case True{} False{}:
          +X1 = List.append(&2, If.Rule, t, b <> a <> post)
          +X2 = List.append(&2, If.Rule, t, a <> b <> post)
          pq.flip({If.look.go(h <> X1, q, d, s, True{}) == If.look.go(h <> X2, q, d, s, False{}) : Maybe<&2, If.Best>}, Bool.and(If.applies(q, h), Nat.is_eq(If.Rule.dir(h), d)), e1, e2)
        case False{} True{}:
          +X1 = List.append(&2, If.Rule, t, b <> a <> post)
          +X2 = List.append(&2, If.Rule, t, a <> b <> post)
          pq.flip({If.look.go(h <> X1, q, d, s, False{}) == If.look.go(h <> X2, q, d, s, True{}) : Maybe<&2, If.Best>}, Bool.and(If.applies(q, h), Nat.is_eq(If.Rule.dir(h), d)), e2, e1)

def pq.amb_tail(pre: List<&2, If.Rule>, +X: List<&2, If.Rule>, h: {If.ambiguous(List.append(&2, If.Rule, pre, X)) == False{} : Bool}) -> {If.ambiguous(X) == False{} : Bool}:
  match pre:
    case Nil{}:
      h
    case +s <> +t:
      +Y = List.append(&2, If.Rule, t, X)
      pq.amb_tail(t, X, pq.or_r(If.clashes(s, Y), If.ambiguous(Y), h))

def pq.quirk_order_free(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +d: Nat, ok: {If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) == True{} : Bool}) -> {If.lookup(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == If.lookup(List.append(&2, If.Rule, pre, a <> b <> post), q, d) : If.Ans}:
  +L1 = List.append(&2, If.Rule, pre, b <> a <> post)
  +L2 = List.append(&2, If.Rule, pre, a <> b <> post)
  +am = pq.not_f(If.ambiguous(L2), pq.and_r(If.known_all(L2, known), Bool.not(If.ambiguous(L2)), ok))
  +ab = pq.amb_tail(pre, a <> b <> post, am)
  +nc = pq.or_l(If.clash(a, b), If.clashes(a, post), pq.or_l(Bool.or(If.clash(a, b), If.clashes(a, post)), If.ambiguous(b <> post), ab))
  +sw = pq.swap_go(pre, a, b, post, q, d, None{}, If.use.at(L1, q, d), If.use.at(L2, q, d), {==}, {==}, nc)
  Equal.cong(Maybe<&2, If.Best>, If.Ans, m => If.ans(m), If.look.go(L1, q, d, None{}, If.use.at(L1, q, d)), If.look.go(L2, q, d, None{}, If.use.at(L2, q, d)), sw)

# The highest layer wins
# ----------------------

# before r: the best is below r's rank, or at it with r's value
def pq.pre_ok(b: Maybe<&2, If.Best>, +r: If.Rule) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case If.Best{+k, v}:
          Bool.or(Nat.is_lt(k, If.Rule.rank(r)), Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r))))

# from r on: the best is at r's rank with r's value
def pq.good(b: Maybe<&2, If.Best>, +r: If.Rule) -> Bool:
  match b:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case If.Best{k, v}:
          Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r)))

def pq.good_ans(b: Maybe<&2, If.Best>, +r: If.Rule, g: {pq.good(b, r) == True{} : Bool}) -> {If.ans(b) == If.Known{If.Rule.val(r)} : If.Ans}:
  match b:
    case None{}:
      pq.absurdF({If.ans(None{}) == If.Known{If.Rule.val(r)} : If.Ans}, g)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          +ev = pq.eq_true(v, If.Rule.val(r), pq.and_r(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r)), g))
          Equal.cong(Nat, If.Ans, z => If.Known{z}, v, If.Rule.val(r), ev)

def pq.good_fresh(+r: If.Rule) -> {pq.good(Some{If.Best{If.Rule.rank(r), If.Rule.val(r)}}, r) == True{} : Bool}:
  +R = If.Rule.rank(r)
  +V = If.Rule.val(r)
  %pq.eq_refl(R) : {Bool.and(_, Nat.is_eq(V, V)) == True{} : Bool}
  %pq.eq_refl(V) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def pq.post_step(b: Maybe<&2, If.Best>, +s: If.Rule, +r: If.Rule, +gb: {pq.good(b, r) == True{} : Bool}, ns: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.good(If.better(b, s), r) == True{} : Bool}:
  match b:
    case None{}:
      pq.absurdF({pq.good(If.better(None{}, s), r) == True{} : Bool}, gb)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          +R = If.Rule.rank(r)
          +ek = pq.eq_true(k, R, pq.and_l(Nat.is_eq(k, R), Nat.is_eq(v, If.Rule.val(r)), gb))
          +lk = pq.lt_at(k, R, If.Rule.rank(s), ek, ns)
          %Equal.sym(Bool, Nat.is_lt(k, If.Rule.rank(s)), False{}, lk) : {pq.good(If.better.at(_, If.Best{k, v}, s), r) == True{} : Bool}
          gb

def pq.post_go(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +r: If.Rule, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, gb: {pq.good(b, r) == True{} : Bool}, +top: {If.any_at(rs, q, d, 1n+If.Rule.rank(r)) == False{} : Bool}) -> {pq.good(If.look.go(rs, q, d, b, hit), r) == True{} : Bool}:
  match rs:
    case Nil{}:
      gb
    case +s <> +rest:
      match hit:
        case True{}:
          +R = If.Rule.rank(r)
          +H = Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), d))
          +z = Nat.is_le(1n+R, If.Rule.rank(s))
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(rest, q, d, 1n+R), top), eh)
          +ns = Equal.trans(Bool, Nat.is_lt(R, If.Rule.rank(s)), z, False{}, pq.lt_le(R, If.Rule.rank(s)), le)
          pq.post_go(rest, q, d, r, If.better(b, s), If.use.at(rest, q, d), {==}, pq.post_step(b, s, r, gb, ns), pq.or_r(Bool.and(H, z), If.any_at(rest, q, d, 1n+R), top))
        case False{}:
          +R = If.Rule.rank(r)
          +H = Bool.and(Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), d)), Nat.is_le(1n+R, If.Rule.rank(s)))
          pq.post_go(rest, q, d, r, b, If.use.at(rest, q, d), {==}, gb, pq.or_r(H, If.any_at(rest, q, d, 1n+R), top))

def pq.at_r_go(+k: Nat, +v: Nat, +r: If.Rule, c: Bool, ec: {Nat.is_lt(k, If.Rule.rank(r)) == c : Bool}, pb: {pq.pre_ok(Some{If.Best{k, v}}, r) == True{} : Bool}) -> {pq.good(If.better.at(c, If.Best{k, v}, r), r) == True{} : Bool}:
  match c:
    case True{}:
      pq.good_fresh(r)
    case False{}:
      pq.or_fl(Nat.is_lt(k, If.Rule.rank(r)), Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r))), pb, ec)

# at r: the best becomes r's rank and value
def pq.at_r(b: Maybe<&2, If.Best>, +r: If.Rule, pb: {pq.pre_ok(b, r) == True{} : Bool}) -> {pq.good(If.better(b, r), r) == True{} : Bool}:
  match b:
    case None{}:
      pq.good_fresh(r)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.at_r_go(k, v, r, Nat.is_lt(k, If.Rule.rank(r)), {==}, pb)

# a rule s before r that applies keeps the best within r
def pq.fresh_ok(+s: If.Rule, +r: If.Rule, +q: If.Query, c: Bool, +ec: {Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)) == c : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(Some{If.Best{If.Rule.rank(s), If.Rule.val(s)}}, r) == True{} : Bool}:
  match c:
    case True{}:
      +RS = If.Rule.rank(s)
      +R = If.Rule.rank(r)
      %Equal.sym(Bool, Nat.is_lt(RS, R), True{}, ec) : {Bool.or(_, Bool.and(Nat.is_eq(RS, R), Nat.is_eq(If.Rule.val(s), If.Rule.val(r)))) == True{} : Bool}
      {==}
    case False{}:
      +RS = If.Rule.rank(s)
      +R = If.Rule.rank(r)
      +VS = If.Rule.val(s)
      +V = If.Rule.val(r)
      +er = pq.tri(RS, R, ts, ec)
      +ev = pq.same_val(q, s, r, If.Rule.dir(r), nc, hs, hr, er)
      %Equal.sym(Bool, Nat.is_lt(RS, R), False{}, ec) : {Bool.or(_, Bool.and(Nat.is_eq(RS, R), Nat.is_eq(VS, V))) == True{} : Bool}
      pq.and_t(Nat.is_eq(RS, R), Nat.is_eq(VS, V), er, pq.eq_of(VS, V, ev))

def pq.pre_at(+k: Nat, +v: Nat, +s: If.Rule, +r: If.Rule, +q: If.Query, c: Bool, pb: {pq.pre_ok(Some{If.Best{k, v}}, r) == True{} : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(If.better.at(c, If.Best{k, v}, s), r) == True{} : Bool}:
  match c:
    case True{}:
      pq.fresh_ok(s, r, q, Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)), {==}, hs, hr, nc, ts)
    case False{}:
      pb

def pq.pre_step(b: Maybe<&2, If.Best>, +s: If.Rule, +r: If.Rule, +q: If.Query, pb: {pq.pre_ok(b, r) == True{} : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(If.better(b, s), r) == True{} : Bool}:
  match b:
    case None{}:
      pq.fresh_ok(s, r, q, Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)), {==}, hs, hr, nc, ts)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.pre_at(k, v, s, r, q, Nat.is_lt(k, If.Rule.rank(s)), pb, hs, hr, nc, ts)

def pq.clashes_mem(+s: If.Rule, t: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, h: {If.clashes(s, List.append(&2, If.Rule, t, r <> post)) == False{} : Bool}) -> {If.clash(s, r) == False{} : Bool}:
  match t:
    case Nil{}:
      pq.or_l(If.clash(s, r), If.clashes(s, post), h)
    case +u <> +t2:
      pq.clashes_mem(s, t2, r, post, pq.or_r(If.clash(s, u), If.clashes(s, List.append(&2, If.Rule, t2, r <> post)), h))

def pq.pre_go(pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +b: Maybe<&2, If.Best>, hit: Bool, +eh: {If.use.at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == hit : Bool}, pb: {pq.pre_ok(b, r) == True{} : Bool}, +top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}, +am: {If.ambiguous(List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}, +hr: {If.applies(q, r) == True{} : Bool}) -> {pq.good(If.look.go(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), b, hit), r) == True{} : Bool}:
  match pre:
    case Nil{}:
      match hit:
        case True{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +H = Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(D, D)), Nat.is_le(1n+R, R))
          pq.post_go(post, q, D, r, If.better(b, r), If.use.at(post, q, D), {==}, pq.at_r(b, r, pb), pq.or_r(H, If.any_at(post, q, D, 1n+R), top))
        case False{}:
          +D = If.Rule.dir(r)
          +hr2 = pq.and_t(If.applies(q, r), Nat.is_eq(D, D), hr, Equal.sym(Bool, True{}, Nat.is_eq(D, D), pq.eq_refl(D)))
          pq.flip({pq.good(If.look.go(r <> post, q, D, b, False{}), r) == True{} : Bool}, Bool.and(If.applies(q, r), Nat.is_eq(D, D)), hr2, eh)
    case +s <> +t:
      match hit:
        case True{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +RS = If.Rule.rank(s)
          +X = List.append(&2, If.Rule, t, r <> post)
          +H = Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), D))
          +z = Nat.is_le(1n+R, RS)
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(X, q, D, 1n+R), top), eh)
          +ts = Equal.trans(Bool, Nat.is_lt(R, RS), z, False{}, pq.lt_le(R, RS), le)
          +nc = pq.clashes_mem(s, t, r, post, pq.or_l(If.clashes(s, X), If.ambiguous(X), am))
          +hr2 = pq.and_t(If.applies(q, r), Nat.is_eq(D, D), hr, Equal.sym(Bool, True{}, Nat.is_eq(D, D), pq.eq_refl(D)))
          +pb2 = pq.pre_step(b, s, r, q, pb, eh, hr2, nc, ts)
          pq.pre_go(t, r, post, q, If.better(b, s), If.use.at(X, q, D), {==}, pb2, pq.or_r(Bool.and(H, z), If.any_at(X, q, D, 1n+R), top), pq.or_r(If.clashes(s, X), If.ambiguous(X), am), hr)
        case False{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +X = List.append(&2, If.Rule, t, r <> post)
          +H = Bool.and(Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), D)), Nat.is_le(1n+R, If.Rule.rank(s)))
          pq.pre_go(t, r, post, q, b, If.use.at(X, q, D), {==}, pb, pq.or_r(H, If.any_at(X, q, D, 1n+R), top), pq.or_r(If.clashes(s, X), If.ambiguous(X), am), hr)

def pq.quirk_highest_wins(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}, hit: {If.applies(q, r) == True{} : Bool}, top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}) -> {If.lookup(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == If.Known{If.Rule.val(r)} : If.Ans}:
  +L = List.append(&2, If.Rule, pre, r <> post)
  +D = If.Rule.dir(r)
  +am = pq.not_f(If.ambiguous(L), pq.and_r(If.known_all(L, known), Bool.not(If.ambiguous(L)), ok))
  +g = pq.pre_go(pre, r, post, q, None{}, If.use.at(L, q, D), {==}, {==}, top, am, hit)
  pq.good_ans(If.look.go(L, q, D, None{}, If.use.at(L, q, D)), r, g)

# The thinking ladder
# -------------------

def pq.quirk_ladder_explicit_first(+e: Ef.LvMap, +rule: Maybe<&2, Ef.LvMap>) -> {If.lad.chosen(Some{e}, rule) == e : Ef.LvMap}:
  {==}

def pq.quirk_ladder_rule_second(+l: Ef.LvMap) -> {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}:
  {==}

def pq.quirk_ladder_default_last() -> {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}:
  {==}

def pq.lad_kb(+l: Ef.Lv, b: Bool) -> {Ef.keep.e(l, If.lad.ent(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pq.lad_kf(+l: Ef.Lv, e: Ef.Ent, +dl: List<&2, Ef.Lv>) -> {Ef.keep.e(l, If.lad.fill.e(l, e, dl)) == If.lad.keep(l, e, dl) : Bool}:
  match e:
    case Ef.Missing{}:
      pq.lad_kb(l, Ef.has(dl, l))
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# the filled map keeps a level exactly when the ladder rule does
def pq.lad_fill_keep(map: Ef.LvMap, +dl: List<&2, Ef.Lv>, l: Ef.Lv) -> {Ef.keep(If.lad.fill(map, dl), l) == If.lad.keep(l, Ef.entry(l, map), dl) : Bool}:
  match map:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      match l:
        case Ef.Off{}:
          pq.lad_kf(Ef.Off{}, o, dl)
        case Ef.Minimal{}:
          pq.lad_kf(Ef.Minimal{}, mi, dl)
        case Ef.Low{}:
          pq.lad_kf(Ef.Low{}, lo, dl)
        case Ef.Medium{}:
          pq.lad_kf(Ef.Medium{}, me, dl)
        case Ef.High{}:
          pq.lad_kf(Ef.High{}, hi, dl)
        case Ef.Xhigh{}:
          pq.lad_kf(Ef.Xhigh{}, xh, dl)
        case Ef.Max{}:
          pq.lad_kf(Ef.Max{}, mx, dl)

def pq.lad_has_keep.at(+map: Ef.LvMap, +l: Ef.Lv, b: Bool, eb: {Ef.keep(map, l) == b : Bool}) -> {Ef.has(Ef.offer(map, Ef.ladder()), l) == b : Bool}:
  match b:
    case True{}:
      Pe.pe.effort_offered_kept(map, l, eb)
    case False{}:
      Pe.pe.offer_out(map, Ef.ladder(), l, Pe.pe.kat(map, Ef.ladder()), {==}, Ef.at(Ef.ladder(), l), {==}, eb)

# a level is in the offer of a map exactly when the map keeps it
def pq.lad_has_keep(+map: Ef.LvMap, +l: Ef.Lv) -> {Ef.has(Ef.offer(map, Ef.ladder()), l) == Ef.keep(map, l) : Bool}:
  pq.lad_has_keep.at(map, l, Ef.keep(map, l), {==})

def pq.quirk_ladder_offered_exact(+explicit: Maybe<&2, Ef.LvMap>, +rule: Maybe<&2, Ef.LvMap>, +d: If.Defaults, +l: Ef.Lv) -> {Ef.has(If.lad.offered(True{}, explicit, rule, d), l) == If.lad.keep(l, Ef.entry(l, If.lad.chosen(explicit, rule)), If.Defaults.reasoning(d)) : Bool}:
  +C = If.lad.chosen(explicit, rule)
  +D = If.Defaults.reasoning(d)
  +F = If.lad.fill(C, D)
  Equal.trans(Bool, Ef.has(Ef.offer(F, Ef.ladder()), l), Ef.keep(F, l), If.lad.keep(l, Ef.entry(l, C), D), pq.lad_has_keep(F, l), pq.lad_fill_keep(C, D, l))

# a map with no entry leaves every level to the default ladder
def pq.lad_none(l: Ef.Lv, +dl: List<&2, Ef.Lv>) -> {If.lad.keep(l, Ef.entry(l, Ef.LvMap.none()), dl) == Ef.has(dl, l) : Bool}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      {==}
    case Ef.Max{}:
      {==}

def pq.quirk_ladder_plain_exact(+explicit: Maybe<&2, Ef.LvMap>, +rule: Maybe<&2, Ef.LvMap>, +d: If.Defaults, +l: Ef.Lv) -> {Ef.has(If.lad.offered(False{}, explicit, rule, d), l) == Ef.has(If.Defaults.plain(d), l) : Bool}:
  +P = If.Defaults.plain(d)
  +N = Ef.LvMap.none()
  +F = If.lad.fill(N, P)
  +k = Equal.trans(Bool, Ef.keep(F, l), If.lad.keep(l, Ef.entry(l, N), P), Ef.has(P, l), pq.lad_fill_keep(N, P, l), pq.lad_none(l, P))
  Equal.trans(Bool, Ef.has(Ef.offer(F, Ef.ladder()), l), Ef.keep(F, l), Ef.has(P, l), pq.lad_has_keep(F, l), k)

# with the shipped default ladder, the ladder rule keeps what S10 keeps
def pq.lad_ship_e(e: Ef.Ent, l: Ef.Lv) -> {If.lad.keep(l, e, If.Defaults.reasoning(If.lad.shipped())) == Ef.keep.e(l, e) : Bool}:
  match e l:
    case Ef.Null{} _:
      {==}
    case Ef.Wire{} _:
      {==}
    case Ef.Missing{} Ef.Off{}:
      {==}
    case Ef.Missing{} Ef.Minimal{}:
      {==}
    case Ef.Missing{} Ef.Low{}:
      {==}
    case Ef.Missing{} Ef.Medium{}:
      {==}
    case Ef.Missing{} Ef.High{}:
      {==}
    case Ef.Missing{} Ef.Xhigh{}:
      {==}
    case Ef.Missing{} Ef.Max{}:
      {==}

def pq.lad_ks(+map: Ef.LvMap, +l: Ef.Lv) -> {Ef.keep(If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped())), l) == Ef.keep(map, l) : Bool}:
  +S = If.Defaults.reasoning(If.lad.shipped())
  Equal.trans(Bool, Ef.keep(If.lad.fill(map, S), l), If.lad.keep(l, Ef.entry(l, map), S), Ef.keep(map, l), pq.lad_fill_keep(map, S, l), pq.lad_ship_e(Ef.entry(l, map), l))

def pq.lad_offer_fill(+map: Ef.LvMap, xs: List<&2, Ef.Lv>) -> {Ef.offer(If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped())), xs) == Ef.offer(map, xs) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      +F = If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped()))
      %pq.lad_ks(map, x) : {Ef.cons_if(Ef.keep(F, x), x, Ef.offer(F, rest)) == Ef.cons_if(_, x, Ef.offer(map, rest)) : List<&2, Ef.Lv>}
      %pq.lad_offer_fill(map, rest) : {Ef.cons_if(Ef.keep(F, x), x, Ef.offer(F, rest)) == Ef.cons_if(Ef.keep(F, x), x, _) : List<&2, Ef.Lv>}
      {==}

def pq.quirk_ladder_shipped_is_s10(r: Bool, +map: Ef.LvMap) -> {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}:
  match r:
    case True{}:
      pq.lad_offer_fill(map, Ef.ladder())
    case False{}:
      {==}
