# proof_effort: the S10 laws (docs/inference.md) of the reasoning-depth
# model in bend/effort.bend.
#
# The offered levels are a filter of the ladder: a level that the filter
# drops (a null entry, a missing xhigh or max) is never in the result, a
# level in the result passes the filter, and a filter keeps the strict
# ascent of the ladder. A clamp keeps a level of the list and else finds
# one in the list, or the head of the list: so it lands in a non-empty
# list, and a second clamp keeps it. A cycle step enters at an offered
# level of a list of two or more; in an ascending list, the scan meets
# that level exactly once, so forward gives the level after it (the head
# after the last) and backward the level before it (the last before the
# head). Every offered level splits the list as pre ++ [l] ++ post, and
# these four steps undo each other. The session stores only fitted
# levels, and a fitted level fits to itself: what the session stores is
# what it sends and shows.
#
# A recursive proof takes the test of the head as a parameter (Bend
# matches only parameters); `pe.kat` computes the filter's test.

import Base
import ./effort.bend as Ef

# Logic
# -----

def pe.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pe.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pe.BD(_, Unit, A)
  Unit{}

def pe.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pe.BD(_, A, Unit)
  Unit{}

def pe.void(-A: Type, e: Empty) -> A:
  match e:

def pe.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pe.absurdF({False{} == True{} : Bool}, h)

def pe.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pe.absurdF({b == True{} : Bool}, h)

def pe.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pe.or_r(x: Bool, +a: Bool, h: {a == True{} : Bool}) -> {Bool.or(x, a) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

# or(c, d) holds and c fails: d holds
def pe.or_l_false(c: Bool, +d: Bool, ec: {c == False{} : Bool}, h: {Bool.or(c, d) == True{} : Bool}) -> {d == True{} : Bool}:
  match c:
    case True{}:
      pe.absurd({d == True{} : Bool}, ec)
    case False{}:
      h

def pe.or_false_l(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

def pe.or_false_r(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {d == False{} : Bool}:
  match c:
    case True{}:
      pe.absurd({d == False{} : Bool}, h)
    case False{}:
      h

def pe.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pe.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Numbers and levels
# ------------------

def pe.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pe.eq_refl(p)

def pe.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pe.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pe.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pe.eq_true(p, q, h))

# a number below another is not it
def pe.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pe.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pe.lt_ne(p, q, h)

# the level at a ladder index
def pe.of(n: Nat) -> Ef.Lv:
  match n:
    case 0n:
      Ef.Off{}
    case 1n+a:
      match a:
        case 0n:
          Ef.Minimal{}
        case 1n+b:
          match b:
            case 0n:
              Ef.Low{}
            case 1n+c:
              match c:
                case 0n:
                  Ef.Medium{}
                case 1n+d:
                  match d:
                    case 0n:
                      Ef.High{}
                    case 1n+e:
                      match e:
                        case 0n:
                          Ef.Xhigh{}
                        case 1n+f:
                          Ef.Max{}

def pe.of_idx(l: Ef.Lv) -> {pe.of(Ef.Lv.idx(l)) == l : Ef.Lv}:
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

def pe.lv_refl(+l: Ef.Lv) -> {True{} == Ef.Lv.eq(l, l) : Bool}:
  pe.eq_refl(Ef.Lv.idx(l))

def pe.lv_true(+a: Ef.Lv, +b: Ef.Lv, h: {Ef.Lv.eq(a, b) == True{} : Bool}) -> {a == b : Ef.Lv}:
  %pe.of_idx(b) : {a == _ : Ef.Lv}
  %pe.eq_true(Ef.Lv.idx(a), Ef.Lv.idx(b), h) : {a == pe.of(_) : Ef.Lv}
  Equal.sym(Ef.Lv, pe.of(Ef.Lv.idx(a)), a, pe.of_idx(a))

# Lists of levels
# ---------------

def pe.has_mid(pre: List<&2, Ef.Lv>, +a: Ef.Lv, +s: List<&2, Ef.Lv>) -> {Ef.has(List.append(&2, Ef.Lv, pre, a <> s), a) == True{} : Bool}:
  match pre:
    case Nil{}:
      %pe.lv_refl(a) : {Bool.or(_, Ef.has(s, a)) == True{} : Bool}
      {==}
    case +x <> +r:
      pe.or_r(Ef.Lv.eq(x, a), Ef.has(List.append(&2, Ef.Lv, r, a <> s), a), pe.has_mid(r, a, s))

def pe.has_app(pre: List<&2, Ef.Lv>, +s: List<&2, Ef.Lv>, +b: Ef.Lv, h: {Ef.has(s, b) == True{} : Bool}) -> {Ef.has(List.append(&2, Ef.Lv, pre, s), b) == True{} : Bool}:
  match pre:
    case Nil{}:
      h
    case +x <> +r:
      pe.or_r(Ef.Lv.eq(x, b), Ef.has(List.append(&2, Ef.Lv, r, s), b), pe.has_app(r, s, b, h))

# a level of ys is above index k when every level of ys is
def pe.above_in(+k: Nat, ys: List<&2, Ef.Lv>, +b: Ef.Lv, c: Bool, ec: {Ef.at(ys, b) == c : Bool}, +ha: {Ef.above(k, ys) == True{} : Bool}, hb: {Ef.has(ys, b) == True{} : Bool}) -> {Nat.is_lt(k, Ef.Lv.idx(b)) == True{} : Bool}:
  match ys:
    case Nil{}:
      pe.absurdF({Nat.is_lt(k, Ef.Lv.idx(b)) == True{} : Bool}, hb)
    case +y <> +r:
      match c:
        case True{}:
          %pe.lv_true(y, b, ec) : {Nat.is_lt(k, Ef.Lv.idx(_)) == True{} : Bool}
          pe.and_l(Nat.is_lt(k, Ef.Lv.idx(y)), Ef.above(k, r), ha)
        case False{}:
          pe.above_in(k, r, b, Ef.at(r, b), {==}, pe.and_r(Nat.is_lt(k, Ef.Lv.idx(y)), Ef.above(k, r), ha), pe.or_l_false(Ef.Lv.eq(y, b), Ef.has(r, b), ec, hb))

# in an ascending pre ++ s, no level of s is in pre
def pe.asc_notin(pre: List<&2, Ef.Lv>, +s: List<&2, Ef.Lv>, +b: Ef.Lv, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, s)) == True{} : Bool}, +hb: {Ef.has(s, b) == True{} : Bool}) -> {Ef.has(pre, b) == False{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case +x <> +r:
      +rs = List.append(&2, Ef.Lv, r, s)
      +lt = pe.above_in(Ef.Lv.idx(x), rs, b, Ef.at(rs, b), {==}, pe.and_l(Ef.above(Ef.Lv.idx(x), rs), Ef.asc(rs), h), pe.has_app(r, s, b, hb))
      %Equal.sym(Bool, Ef.Lv.eq(x, b), False{}, pe.lt_ne(Ef.Lv.idx(x), Ef.Lv.idx(b), lt)) : {Bool.or(_, Ef.has(r, b)) == False{} : Bool}
      pe.asc_notin(r, s, b, pe.and_r(Ef.above(Ef.Lv.idx(x), rs), Ef.asc(rs), h), hb)

# a suffix of an ascending list ascends
def pe.asc_suf(pre: List<&2, Ef.Lv>, +s: List<&2, Ef.Lv>, h: {Ef.asc(List.append(&2, Ef.Lv, pre, s)) == True{} : Bool}) -> {Ef.asc(s) == True{} : Bool}:
  match pre:
    case Nil{}:
      h
    case +x <> +r:
      +rs = List.append(&2, Ef.Lv, r, s)
      pe.asc_suf(r, s, pe.and_r(Ef.above(Ef.Lv.idx(x), rs), Ef.asc(rs), h))

def pe.asc_tr(-xs: List<&2, Ef.Lv>, -ys: List<&2, Ef.Lv>, e: {xs == ys : List<&2, Ef.Lv>}, h: {Ef.asc(xs) == True{} : Bool}) -> {Ef.asc(ys) == True{} : Bool}:
  %e : {Ef.asc(_) == True{} : Bool}
  h

def pe.last_snoc(xs: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Lv) -> {Ef.last(List.append(&2, Ef.Lv, xs, [l]), d) == l : Ef.Lv}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      pe.last_snoc(r, l, x)

def pe.app_snoc(xs: List<&2, Ef.Lv>, +a: Ef.Lv, +ys: List<&2, Ef.Lv>) -> {List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, xs, [a]), ys) == List.append(&2, Ef.Lv, xs, a <> ys) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, zs => x <> zs, List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, r, [a]), ys), List.append(&2, Ef.Lv, r, a <> ys), pe.app_snoc(r, a, ys))

# x <> r without its last level
def pe.init(r: List<&2, Ef.Lv>, x: Ef.Lv) -> List<&2, Ef.Lv>:
  match r:
    case Nil{}:
      Nil{}
    case y <> s:
      x <> pe.init(s, y)

def pe.init_last(r: List<&2, Ef.Lv>, +x: Ef.Lv) -> {x <> r == List.append(&2, Ef.Lv, pe.init(r, x), [Ef.last(r, x)]) : List<&2, Ef.Lv>}:
  match r:
    case Nil{}:
      {==}
    case +y <> +s:
      Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, zs => x <> zs, y <> s, List.append(&2, Ef.Lv, pe.init(s, y), [Ef.last(s, y)]), pe.init_last(s, y))

# The offered levels
# ------------------

# the filter's test of the head of xs
def pe.kat(+map: Ef.LvMap, xs: List<&2, Ef.Lv>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Ef.keep(map, x)

# a level the filter drops is not in its result
def pe.offer_out(+map: Ef.LvMap, xs: List<&2, Ef.Lv>, +l: Ef.Lv, b: Bool, eb: {pe.kat(map, xs) == b : Bool}, c: Bool, ec: {Ef.at(xs, l) == c : Bool}, +nk: {Ef.keep(map, l) == False{} : Bool}) -> {Ef.has(Ef.offer(map, xs), l) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match b:
        case True{}:
          match c:
            case True{}:
              +same = Equal.cong(Ef.Lv, Bool, v => Ef.keep(map, v), x, l, pe.lv_true(x, l, ec))
              pe.absurd({Ef.has(Ef.offer(map, x <> r), l) == False{} : Bool}, Equal.trans(Bool, True{}, Ef.keep(map, l), False{}, Equal.trans(Bool, True{}, Ef.keep(map, x), Ef.keep(map, l), Equal.sym(Bool, Ef.keep(map, x), True{}, eb), same), nk))
            case False{}:
              %Equal.sym(Bool, Ef.keep(map, x), True{}, eb) : {Ef.has(Ef.cons_if(_, x, Ef.offer(map, r)), l) == False{} : Bool}
              %Equal.sym(Bool, Ef.Lv.eq(x, l), False{}, ec) : {Bool.or(_, Ef.has(Ef.offer(map, r), l)) == False{} : Bool}
              pe.offer_out(map, r, l, pe.kat(map, r), {==}, Ef.at(r, l), {==}, nk)
        case False{}:
          %Equal.sym(Bool, Ef.keep(map, x), False{}, eb) : {Ef.has(Ef.cons_if(_, x, Ef.offer(map, r)), l) == False{} : Bool}
          pe.offer_out(map, r, l, pe.kat(map, r), {==}, Ef.at(r, l), {==}, nk)

# a level in the filter's result passes the filter
def pe.offer_in.at(+map: Ef.LvMap, +xs: List<&2, Ef.Lv>, +l: Ef.Lv, k: Bool, ek: {Ef.keep(map, l) == k : Bool}, h: {Ef.has(Ef.offer(map, xs), l) == True{} : Bool}) -> {Ef.keep(map, l) == True{} : Bool}:
  match k:
    case True{}:
      ek
    case False{}:
      +out = pe.offer_out(map, xs, l, pe.kat(map, xs), {==}, Ef.at(xs, l), {==}, ek)
      pe.absurd({Ef.keep(map, l) == True{} : Bool}, Equal.trans(Bool, True{}, Ef.has(Ef.offer(map, xs), l), False{}, Equal.sym(Bool, Ef.has(Ef.offer(map, xs), l), True{}, h), out))

def pe.offer_in(+map: Ef.LvMap, +xs: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.has(Ef.offer(map, xs), l) == True{} : Bool}) -> {Ef.keep(map, l) == True{} : Bool}:
  pe.offer_in.at(map, xs, l, Ef.keep(map, l), {==}, h)

def pe.offer_above(+k: Nat, +map: Ef.LvMap, xs: List<&2, Ef.Lv>, b: Bool, eb: {pe.kat(map, xs) == b : Bool}, +ha: {Ef.above(k, xs) == True{} : Bool}) -> {Ef.above(k, Ef.offer(map, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match b:
        case True{}:
          %Equal.sym(Bool, Ef.keep(map, x), True{}, eb) : {Ef.above(k, Ef.cons_if(_, x, Ef.offer(map, r))) == True{} : Bool}
          +ih = pe.offer_above(k, map, r, pe.kat(map, r), {==}, pe.and_r(Nat.is_lt(k, Ef.Lv.idx(x)), Ef.above(k, r), ha))
          pe.and_t(Nat.is_lt(k, Ef.Lv.idx(x)), Ef.above(k, Ef.offer(map, r)), pe.and_l(Nat.is_lt(k, Ef.Lv.idx(x)), Ef.above(k, r), ha), ih)
        case False{}:
          %Equal.sym(Bool, Ef.keep(map, x), False{}, eb) : {Ef.above(k, Ef.cons_if(_, x, Ef.offer(map, r))) == True{} : Bool}
          pe.offer_above(k, map, r, pe.kat(map, r), {==}, pe.and_r(Nat.is_lt(k, Ef.Lv.idx(x)), Ef.above(k, r), ha))

def pe.offer_asc(+map: Ef.LvMap, xs: List<&2, Ef.Lv>, b: Bool, eb: {pe.kat(map, xs) == b : Bool}, +h: {Ef.asc(xs) == True{} : Bool}) -> {Ef.asc(Ef.offer(map, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match b:
        case True{}:
          %Equal.sym(Bool, Ef.keep(map, x), True{}, eb) : {Ef.asc(Ef.cons_if(_, x, Ef.offer(map, r))) == True{} : Bool}
          +ih = pe.offer_asc(map, r, pe.kat(map, r), {==}, pe.and_r(Ef.above(Ef.Lv.idx(x), r), Ef.asc(r), h))
          +ab = pe.offer_above(Ef.Lv.idx(x), map, r, pe.kat(map, r), {==}, pe.and_l(Ef.above(Ef.Lv.idx(x), r), Ef.asc(r), h))
          pe.and_t(Ef.above(Ef.Lv.idx(x), Ef.offer(map, r)), Ef.asc(Ef.offer(map, r)), ab, ih)
        case False{}:
          %Equal.sym(Bool, Ef.keep(map, x), False{}, eb) : {Ef.asc(Ef.cons_if(_, x, Ef.offer(map, r))) == True{} : Bool}
          pe.offer_asc(map, r, pe.kat(map, r), {==}, pe.and_r(Ef.above(Ef.Lv.idx(x), r), Ef.asc(r), h))

# a level of xs that passes the filter is in its result
def pe.offer_keep(+map: Ef.LvMap, xs: List<&2, Ef.Lv>, +l: Ef.Lv, b: Bool, eb: {pe.kat(map, xs) == b : Bool}, c: Bool, +ec: {Ef.at(xs, l) == c : Bool}, +k: {Ef.keep(map, l) == True{} : Bool}, in: {Ef.has(xs, l) == True{} : Bool}) -> {Ef.has(Ef.offer(map, xs), l) == True{} : Bool}:
  match xs:
    case Nil{}:
      pe.absurdF({Ef.has(Nil{}, l) == True{} : Bool}, in)
    case +x <> +r:
      match b:
        case True{}:
          match c:
            case True{}:
              %Equal.sym(Bool, Ef.keep(map, x), True{}, eb) : {Ef.has(Ef.cons_if(_, x, Ef.offer(map, r)), l) == True{} : Bool}
              %Equal.sym(Bool, Ef.Lv.eq(x, l), True{}, ec) : {Bool.or(_, Ef.has(Ef.offer(map, r), l)) == True{} : Bool}
              {==}
            case False{}:
              %Equal.sym(Bool, Ef.keep(map, x), True{}, eb) : {Ef.has(Ef.cons_if(_, x, Ef.offer(map, r)), l) == True{} : Bool}
              %Equal.sym(Bool, Ef.Lv.eq(x, l), False{}, ec) : {Bool.or(_, Ef.has(Ef.offer(map, r), l)) == True{} : Bool}
              pe.offer_keep(map, r, l, pe.kat(map, r), {==}, Ef.at(r, l), {==}, k, pe.or_l_false(Ef.Lv.eq(x, l), Ef.has(r, l), ec, in))
        case False{}:
          match c:
            case True{}:
              +same = Equal.cong(Ef.Lv, Bool, v => Ef.keep(map, v), x, l, pe.lv_true(x, l, ec))
              pe.absurdF({Ef.has(Ef.offer(map, x <> r), l) == True{} : Bool}, Equal.trans(Bool, False{}, Ef.keep(map, l), True{}, Equal.trans(Bool, False{}, Ef.keep(map, x), Ef.keep(map, l), Equal.sym(Bool, Ef.keep(map, x), False{}, eb), same), k))
            case False{}:
              %Equal.sym(Bool, Ef.keep(map, x), False{}, eb) : {Ef.has(Ef.cons_if(_, x, Ef.offer(map, r)), l) == True{} : Bool}
              pe.offer_keep(map, r, l, pe.kat(map, r), {==}, Ef.at(r, l), {==}, k, pe.or_l_false(Ef.Lv.eq(x, l), Ef.has(r, l), ec, in))

# every level is on the ladder
def pe.on_ladder(l: Ef.Lv) -> {Ef.has(Ef.ladder(), l) == True{} : Bool}:
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

# a level kept with entry e that is xhigh or max has a wire entry
def pe.wire(+l: Ef.Lv, e: Ef.Ent, x: {Ef.ext(l) == True{} : Bool}, k: {Ef.keep.e(l, e) == True{} : Bool}) -> {e == Ef.Wire{} : Ef.Ent}:
  match e:
    case Ef.Missing{}:
      +nx = pe.not_t(Ef.ext(l), k)
      pe.absurd({Ef.Missing{} == Ef.Wire{} : Ef.Ent}, Equal.trans(Bool, True{}, Ef.ext(l), False{}, Equal.sym(Bool, Ef.ext(l), True{}, x), nx))
    case Ef.Null{}:
      pe.absurdF({Ef.Null{} == Ef.Wire{} : Ef.Ent}, k)
    case Ef.Wire{}:
      {==}

def pe.or_false_t(c: Bool, h: {Bool.or(c, False{}) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

# The clamp
# ---------

def pe.first_in(lad: List<&2, Ef.Lv>, ne: {Ef.empty(lad) == False{} : Bool}) -> {Ef.has(lad, Ef.first(lad, Ef.Off{})) == True{} : Bool}:
  match lad:
    case Nil{}:
      pe.absurd({Ef.has(Nil{}, Ef.Off{}) == True{} : Bool}, ne)
    case +h <> t:
      %pe.lv_refl(h) : {Bool.or(_, Ef.has(t, h)) == True{} : Bool}
      {==}

def pe.find_in(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +d: Ef.Lv, hit: Bool, eh: {Ef.in.at(xs, lad) == hit : Bool}, hd: {Ef.has(lad, d) == True{} : Bool}) -> {Ef.has(lad, Ef.find.go(xs, lad, d, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hd
    case +x <> +r:
      match hit:
        case True{}:
          eh
        case False{}:
          pe.find_in(r, lad, d, Ef.in.at(r, lad), {==}, hd)

def pe.find_nil(xs: List<&2, Ef.Lv>, +d: Ef.Lv, hit: Bool, eh: {Ef.in.at(xs, Nil{}) == hit : Bool}) -> {Ef.find.go(xs, Nil{}, d, hit) == d : Ef.Lv}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match hit:
        case True{}:
          pe.absurdF({x == d : Ef.Lv}, eh)
        case False{}:
          pe.find_nil(r, d, Ef.in.at(r, Nil{}), {==})

def pe.clamp_in.at(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, eb: {Ef.has(lad, l) == b : Bool}, ne: {Ef.empty(lad) == False{} : Bool}) -> {Ef.has(lad, Ef.clamp.at(b, l, lad)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      pe.find_in(Ef.scan(l), lad, Ef.first(lad, Ef.Off{}), Ef.in.at(Ef.scan(l), lad), {==}, pe.first_in(lad, ne))

def pe.clamp_in(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, ne: {Ef.empty(lad) == False{} : Bool}) -> {Ef.has(lad, Ef.clamp.in(lad, l)) == True{} : Bool}:
  pe.clamp_in.at(Ef.has(lad, l), lad, l, {==}, ne)

def pe.clamp_keep(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, in: {Ef.has(lad, l) == True{} : Bool}) -> {Ef.clamp.in(lad, l) == l : Ef.Lv}:
  %Equal.sym(Bool, Ef.has(lad, l), True{}, in) : {Ef.clamp.at(_, l, lad) == l : Ef.Lv}
  {==}

def pe.clamp_nil(+l: Ef.Lv) -> {Ef.clamp.in(Nil{}, l) == Ef.Off{} : Ef.Lv}:
  pe.find_nil(Ef.scan(l), Ef.Off{}, Ef.in.at(Ef.scan(l), Nil{}), {==})

def pe.clamp_idem(lad: List<&2, Ef.Lv>, +l: Ef.Lv) -> {Ef.clamp.in(lad, Ef.clamp.in(lad, l)) == Ef.clamp.in(lad, l) : Ef.Lv}:
  match lad:
    case Nil{}:
      %Equal.sym(Ef.Lv, Ef.clamp.in(Nil{}, l), Ef.Off{}, pe.clamp_nil(l)) : {Ef.clamp.in(Nil{}, _) == _ : Ef.Lv}
      pe.clamp_nil(Ef.Off{})
    case +h <> +t:
      pe.clamp_keep(h <> t, Ef.clamp.in(h <> t, l), pe.clamp_in(h <> t, l, {==}))

# The cycle
# ---------

def pe.two_app(+x: Ef.Lv, r: List<&2, Ef.Lv>, +a: Ef.Lv, +s: List<&2, Ef.Lv>) -> {Ef.two(x <> List.append(&2, Ef.Lv, r, a <> s)) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case y <> q:
      {==}

def pe.two_mid(pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>) -> {Ef.two(List.append(&2, Ef.Lv, pre, a <> b <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case x <> r:
      pe.two_app(x, r, a, b <> post)

# a step of a list of two or more from a level of the list starts there
def pe.enter(+lad: List<&2, Ef.Lv>, +c: Ef.Lv, +d: Ef.Dir, tw: {Ef.two(lad) == True{} : Bool}, in: {Ef.has(lad, c) == True{} : Bool}) -> {Ef.cycle.in(lad, c, d) == Ef.move(d, lad, c) : Maybe<&2, Ef.Lv>}:
  %Equal.sym(Bool, Ef.two(lad), True{}, tw) : {Ef.cycle.at(_, lad, c, d) == Ef.move(d, lad, c) : Maybe<&2, Ef.Lv>}
  %Equal.sym(Ef.Lv, Ef.clamp.in(lad, c), c, pe.clamp_keep(lad, c, in)) : {Ef.move(d, lad, _) == Ef.move(d, lad, c) : Maybe<&2, Ef.Lv>}
  {==}

# forward from a, which pre lacks, gives the level after it
def pe.fwd_go(pre: List<&2, Ef.Lv>, +a: Ef.Lv, +post: List<&2, Ef.Lv>, +top: Ef.Lv, hit: Bool, eh: {Ef.at(List.append(&2, Ef.Lv, pre, a <> post), a) == hit : Bool}, out: {Ef.has(pre, a) == False{} : Bool}) -> {Ef.fwd.go(List.append(&2, Ef.Lv, pre, a <> post), a, top, hit) == Some{Ef.first(post, top)} : Maybe<&2, Ef.Lv>}:
  match pre:
    case Nil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          pe.absurd({Ef.fwd.go(a <> post, a, top, False{}) == Some{Ef.first(post, top)} : Maybe<&2, Ef.Lv>}, Equal.trans(Bool, True{}, Ef.Lv.eq(a, a), False{}, pe.lv_refl(a), eh))
    case +x <> +r:
      match hit:
        case True{}:
          +nx = pe.or_false_l(Ef.Lv.eq(x, a), Ef.has(r, a), out)
          pe.absurd({Ef.fwd.go(x <> List.append(&2, Ef.Lv, r, a <> post), a, top, True{}) == Some{Ef.first(post, top)} : Maybe<&2, Ef.Lv>}, Equal.trans(Bool, True{}, Ef.Lv.eq(x, a), False{}, Equal.sym(Bool, Ef.Lv.eq(x, a), True{}, eh), nx))
        case False{}:
          pe.fwd_go(r, a, post, top, Ef.at(List.append(&2, Ef.Lv, r, a <> post), a), {==}, pe.or_false_r(Ef.Lv.eq(x, a), Ef.has(r, a), out))

# backward from b, which pre lacks, right after a, gives a
def pe.bwd_go(pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, prev: Ef.Lv, hit: Bool, eh: {Ef.at(List.append(&2, Ef.Lv, pre, a <> b <> post), b) == hit : Bool}, out: {Ef.has(pre, b) == False{} : Bool}, +ne: {Ef.Lv.eq(a, b) == False{} : Bool}) -> {Ef.bwd.go(List.append(&2, Ef.Lv, pre, a <> b <> post), b, prev, hit) == Some{a} : Maybe<&2, Ef.Lv>}:
  match pre:
    case Nil{}:
      match hit:
        case True{}:
          pe.absurd({Ef.bwd.go(a <> b <> post, b, prev, True{}) == Some{a} : Maybe<&2, Ef.Lv>}, Equal.trans(Bool, True{}, Ef.Lv.eq(a, b), False{}, Equal.sym(Bool, Ef.Lv.eq(a, b), True{}, eh), ne))
        case False{}:
          %pe.lv_refl(b) : {Ef.bwd.go(b <> post, b, a, _) == Some{a} : Maybe<&2, Ef.Lv>}
          {==}
    case +x <> +r:
      match hit:
        case True{}:
          +nx = pe.or_false_l(Ef.Lv.eq(x, b), Ef.has(r, b), out)
          pe.absurd({Ef.bwd.go(x <> List.append(&2, Ef.Lv, r, a <> b <> post), b, prev, True{}) == Some{a} : Maybe<&2, Ef.Lv>}, Equal.trans(Bool, True{}, Ef.Lv.eq(x, b), False{}, Equal.sym(Bool, Ef.Lv.eq(x, b), True{}, eh), nx))
        case False{}:
          pe.bwd_go(r, a, b, post, x, Ef.at(List.append(&2, Ef.Lv, r, a <> b <> post), b), {==}, pe.or_false_r(Ef.Lv.eq(x, b), Ef.has(r, b), out), ne)

# in an ascending pre ++ [a, b] ++ post, forward from a gives b
def pe.next(+pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, h: {Ef.asc(List.append(&2, Ef.Lv, pre, a <> b <> post)) == True{} : Bool}) -> {Ef.cycle.in(List.append(&2, Ef.Lv, pre, a <> b <> post), a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}:
  +lad = List.append(&2, Ef.Lv, pre, a <> b <> post)
  +out = pe.asc_notin(pre, a <> b <> post, a, h, pe.has_mid(Nil{}, a, b <> post))
  Equal.trans(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, a, Ef.Forward{}), Ef.move(Ef.Forward{}, lad, a), Some{b}, pe.enter(lad, a, Ef.Forward{}, pe.two_mid(pre, a, b, post), pe.has_mid(pre, a, b <> post)), pe.fwd_go(pre, a, b <> post, Ef.first(lad, Ef.Off{}), Ef.at(lad, a), {==}, out))

# in an ascending pre ++ [a, b] ++ post, backward from b gives a
def pe.prev(+pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, a <> b <> post)) == True{} : Bool}) -> {Ef.cycle.in(List.append(&2, Ef.Lv, pre, a <> b <> post), b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}:
  +lad = List.append(&2, Ef.Lv, pre, a <> b <> post)
  +hb = pe.or_r(Ef.Lv.eq(a, b), Ef.has(b <> post, b), pe.has_mid(Nil{}, b, post))
  +out = pe.asc_notin(pre, a <> b <> post, b, h, hb)
  +sa = pe.asc_suf(pre, a <> b <> post, h)
  +ab = pe.and_l(Ef.above(Ef.Lv.idx(a), b <> post), Ef.asc(b <> post), sa)
  +ne = pe.lt_ne(Ef.Lv.idx(a), Ef.Lv.idx(b), pe.and_l(Nat.is_lt(Ef.Lv.idx(a), Ef.Lv.idx(b)), Ef.above(Ef.Lv.idx(a), post), ab))
  Equal.trans(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, b, Ef.Backward{}), Ef.move(Ef.Backward{}, lad, b), Some{a}, pe.enter(lad, b, Ef.Backward{}, pe.two_mid(pre, a, b, post), pe.has_app(pre, a <> b <> post, b, hb)), pe.bwd_go(pre, a, b, post, Ef.last(lad, Ef.Off{}), Ef.at(lad, b), {==}, out, ne))

# in an ascending (h0 <> pre) ++ [z], forward from z gives h0
def pe.wrap(+h0: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv, h: {Ef.asc(List.append(&2, Ef.Lv, h0 <> pre, [z])) == True{} : Bool}) -> {Ef.cycle.in(List.append(&2, Ef.Lv, h0 <> pre, [z]), z, Ef.Forward{}) == Some{h0} : Maybe<&2, Ef.Lv>}:
  +lad = List.append(&2, Ef.Lv, h0 <> pre, [z])
  +out = pe.asc_notin(h0 <> pre, [z], z, h, pe.has_mid(Nil{}, z, Nil{}))
  Equal.trans(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, z, Ef.Forward{}), Ef.move(Ef.Forward{}, lad, z), Some{h0}, pe.enter(lad, z, Ef.Forward{}, pe.two_app(h0, pre, z, Nil{}), pe.has_mid(h0 <> pre, z, Nil{})), pe.fwd_go(h0 <> pre, z, Nil{}, Ef.first(lad, Ef.Off{}), Ef.at(lad, z), {==}, out))

def pe.head_go(+h0: Ef.Lv, +rest: List<&2, Ef.Lv>) -> {Ef.bwd.go(h0 <> rest, h0, Ef.last(rest, h0), Ef.Lv.eq(h0, h0)) == Some{Ef.last(rest, h0)} : Maybe<&2, Ef.Lv>}:
  %pe.lv_refl(h0) : {Ef.bwd.go(h0 <> rest, h0, Ef.last(rest, h0), _) == Some{Ef.last(rest, h0)} : Maybe<&2, Ef.Lv>}
  {==}

# in (h0 <> pre) ++ [z], backward from h0 gives z
def pe.wrap_back(+h0: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv) -> {Ef.cycle.in(List.append(&2, Ef.Lv, h0 <> pre, [z]), h0, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}:
  +lad = List.append(&2, Ef.Lv, h0 <> pre, [z])
  +rest = List.append(&2, Ef.Lv, pre, [z])
  +go = Equal.trans(Maybe<&2, Ef.Lv>, Ef.move(Ef.Backward{}, lad, h0), Some{Ef.last(rest, h0)}, Some{z}, pe.head_go(h0, rest), Equal.cong(Ef.Lv, Maybe<&2, Ef.Lv>, v => Some{v}, Ef.last(rest, h0), z, pe.last_snoc(pre, z, h0)))
  Equal.trans(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, h0, Ef.Backward{}), Ef.move(Ef.Backward{}, lad, h0), Some{z}, pe.enter(lad, h0, Ef.Backward{}, pe.two_app(h0, pre, z, Nil{}), pe.has_mid(Nil{}, h0, rest)), go)

# Inverse steps
# -------------

# one cycle step along lad from x, x itself when the step changes nothing
def pe.tl(+lad: List<&2, Ef.Lv>, +x: Ef.Lv, d: Ef.Dir) -> Ef.Lv:
  Maybe.default(&2, Ef.Lv, Ef.cycle.in(lad, x, d), x)

def pe.tl_two(+lad: List<&2, Ef.Lv>, +x: Ef.Lv, +y: Ef.Lv, +d1: Ef.Dir, +d2: Ef.Dir, e1: {Ef.cycle.in(lad, x, d1) == Some{y} : Maybe<&2, Ef.Lv>}, e2: {Ef.cycle.in(lad, y, d2) == Some{x} : Maybe<&2, Ef.Lv>}) -> {pe.tl(lad, pe.tl(lad, x, d1), d2) == x : Ef.Lv}:
  %Equal.sym(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, x, d1), Some{y}, e1) : {Maybe.default(&2, Ef.Lv, Ef.cycle.in(lad, Maybe.default(&2, Ef.Lv, _, x), d2), Maybe.default(&2, Ef.Lv, _, x)) == x : Ef.Lv}
  %Equal.sym(Maybe<&2, Ef.Lv>, Ef.cycle.in(lad, y, d2), Some{x}, e2) : {Maybe.default(&2, Ef.Lv, _, y) == x : Ef.Lv}
  {==}

# backward undoes forward on an ascending pre ++ [l] ++ post
def pe.bf(pre: List<&2, Ef.Lv>, +l: Ef.Lv, post: List<&2, Ef.Lv>, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, l <> post)) == True{} : Bool}) -> {pe.tl(List.append(&2, Ef.Lv, pre, l <> post), pe.tl(List.append(&2, Ef.Lv, pre, l <> post), l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  match pre:
    case Nil{}:
      match post:
        case Nil{}:
          {==}
        case +b <> +q:
          pe.tl_two(l <> b <> q, l, b, Ef.Forward{}, Ef.Backward{}, pe.next(Nil{}, l, b, q, h), pe.prev(Nil{}, l, b, q, h))
    case +x <> +r:
      match post:
        case Nil{}:
          pe.tl_two(List.append(&2, Ef.Lv, x <> r, [l]), l, x, Ef.Forward{}, Ef.Backward{}, pe.wrap(x, r, l, h), pe.wrap_back(x, r, l))
        case +b <> +q:
          pe.tl_two(List.append(&2, Ef.Lv, x <> r, l <> b <> q), l, b, Ef.Forward{}, Ef.Backward{}, pe.next(x <> r, l, b, q, h), pe.prev(x <> r, l, b, q, h))

# forward undoes backward on an ascending pre ++ [l] ++ post
def pe.fb(pre: List<&2, Ef.Lv>, +l: Ef.Lv, +post: List<&2, Ef.Lv>, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, l <> post)) == True{} : Bool}) -> {pe.tl(List.append(&2, Ef.Lv, pre, l <> post), pe.tl(List.append(&2, Ef.Lv, pre, l <> post), l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  match pre:
    case Nil{}:
      match post:
        case Nil{}:
          {==}
        case +p <> +ps:
          +i = pe.init(ps, p)
          +z = Ef.last(ps, p)
          +e = pe.init_last(ps, p)
          %Equal.sym(List<&2, Ef.Lv>, p <> ps, List.append(&2, Ef.Lv, i, [z]), e) : {pe.tl(l <> _, pe.tl(l <> _, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
          +h2 = pe.asc_tr(l <> p <> ps, l <> List.append(&2, Ef.Lv, i, [z]), Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, ys => l <> ys, p <> ps, List.append(&2, Ef.Lv, i, [z]), e), h)
          pe.tl_two(List.append(&2, Ef.Lv, l <> i, [z]), l, z, Ef.Backward{}, Ef.Forward{}, pe.wrap_back(l, i, z), pe.wrap(l, i, z, h2))
    case +x <> +r:
      +i = pe.init(r, x)
      +a = Ef.last(r, x)
      +tail = {l <> post : List<&2, Ef.Lv>}
      +c1 = Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, ys => List.append(&2, Ef.Lv, ys, tail), x <> r, List.append(&2, Ef.Lv, i, [a]), pe.init_last(r, x))
      +e = Equal.trans(List<&2, Ef.Lv>, List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, i, [a]), tail), List.append(&2, Ef.Lv, i, a <> tail), c1, pe.app_snoc(i, a, tail))
      %Equal.sym(List<&2, Ef.Lv>, List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, i, a <> tail), e) : {pe.tl(_, pe.tl(_, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
      +h2 = pe.asc_tr(List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, i, a <> tail), e, h)
      pe.tl_two(List.append(&2, Ef.Lv, i, a <> l <> post), l, a, Ef.Backward{}, Ef.Forward{}, pe.prev(i, a, l, post, h2), pe.next(i, a, l, post, h2))

# the levels of xs before its first l
def pe.spre(xs: List<&2, Ef.Lv>, +l: Ef.Lv, hit: Bool) -> List<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> +r:
      match hit:
        case True{}:
          Nil{}
        case False{}:
          x <> pe.spre(r, l, Ef.at(r, l))

# the levels of xs after its first l
def pe.spost(xs: List<&2, Ef.Lv>, +l: Ef.Lv, hit: Bool) -> List<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> +r:
      match hit:
        case True{}:
          r
        case False{}:
          pe.spost(r, l, Ef.at(r, l))

# a list that has l splits at its first l
def pe.split(xs: List<&2, Ef.Lv>, +l: Ef.Lv, hit: Bool, eh: {Ef.at(xs, l) == hit : Bool}, in: {Ef.has(xs, l) == True{} : Bool}) -> {xs == List.append(&2, Ef.Lv, pe.spre(xs, l, hit), l <> pe.spost(xs, l, hit)) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      pe.absurdF({Nil{} == [l] : List<&2, Ef.Lv>}, in)
    case +x <> +r:
      match hit:
        case True{}:
          %pe.lv_true(x, l, eh) : {x <> r == _ <> r : List<&2, Ef.Lv>}
          {==}
        case False{}:
          +ih = pe.split(r, l, Ef.at(r, l), {==}, pe.or_l_false(Ef.Lv.eq(x, l), Ef.has(r, l), eh, in))
          Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, ys => x <> ys, r, List.append(&2, Ef.Lv, pe.spre(r, l, Ef.at(r, l)), l <> pe.spost(r, l, Ef.at(r, l))), ih)

def pe.bf_any(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.asc(lad) == True{} : Bool}, in: {Ef.has(lad, l) == True{} : Bool}) -> {pe.tl(lad, pe.tl(lad, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  +pre = pe.spre(lad, l, Ef.at(lad, l))
  +post = pe.spost(lad, l, Ef.at(lad, l))
  +e = pe.split(lad, l, Ef.at(lad, l), {==}, in)
  %Equal.sym(List<&2, Ef.Lv>, lad, List.append(&2, Ef.Lv, pre, l <> post), e) : {pe.tl(_, pe.tl(_, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}
  pe.bf(pre, l, post, pe.asc_tr(lad, List.append(&2, Ef.Lv, pre, l <> post), e, h))

def pe.fb_any(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.asc(lad) == True{} : Bool}, in: {Ef.has(lad, l) == True{} : Bool}) -> {pe.tl(lad, pe.tl(lad, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  +pre = pe.spre(lad, l, Ef.at(lad, l))
  +post = pe.spost(lad, l, Ef.at(lad, l))
  +e = pe.split(lad, l, Ef.at(lad, l), {==}, in)
  %Equal.sym(List<&2, Ef.Lv>, lad, List.append(&2, Ef.Lv, pre, l <> post), e) : {pe.tl(_, pe.tl(_, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
  pe.fb(pre, l, post, pe.asc_tr(lad, List.append(&2, Ef.Lv, pre, l <> post), e, h))

# The session
# -----------

# the session holds a level that fits to itself
def pe.Fixed(s: Ef.Sess) -> Type:
  match s:
    case Ef.Sess{mo, st}:
      match st:
        case None{}:
          Empty
        case Some{l}:
          {Ef.fit(mo, l) == l : Ef.Lv}

def pe.fit_idem(mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv) -> {Ef.fit(mo, Ef.fit(mo, l)) == Ef.fit(mo, l) : Ef.Lv}:
  match mo:
    case None{}:
      {==}
    case Some{+m}:
      pe.clamp_idem(Ef.offered(m), l)

def pe.open_fix(s: Ef.Sess, +dflt: Ef.Lv) -> pe.Fixed(Ef.open(s, dflt)):
  match s:
    case Ef.Sess{+mo, st}:
      pe.fit_idem(mo, Maybe.default(&2, Ef.Lv, st, dflt))

def pe.step_fix(+m: Ef.Mdl, r: Maybe<&2, Ef.Lv>, +l: Ef.Lv, fx: {Ef.clamp(m, l) == l : Ef.Lv}) -> {Ef.clamp(m, Ef.step.set(m, r, l)) == Ef.step.set(m, r, l) : Ef.Lv}:
  match r:
    case None{}:
      fx
    case Some{k}:
      pe.clamp_idem(Ef.offered(m), k)

def pe.steplv_fix(mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv, +d: Ef.Dir, fx: {Ef.fit(mo, l) == l : Ef.Lv}) -> {Ef.fit(mo, Ef.step.lv(mo, l, d)) == Ef.step.lv(mo, l, d) : Ef.Lv}:
  match mo:
    case None{}:
      {==}
    case Some{+m}:
      pe.step_fix(m, Ef.cycle(m, l, d), l, fx)

def pe.actset_fix(a: Ef.Act, +mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv, fx: {Ef.fit(mo, l) == l : Ef.Lv}) -> pe.Fixed(Ef.act.set(a, mo, l)):
  match a:
    case Ef.Switch{+m}:
      pe.clamp_idem(Ef.offered(m), l)
    case Ef.SetLevel{k}:
      pe.fit_idem(mo, k)
    case Ef.Step{d}:
      pe.steplv_fix(mo, l, d, fx)

def pe.act_fix(s: Ef.Sess, a: Ef.Act, f: pe.Fixed(s)) -> pe.Fixed(Ef.act(a, s)):
  match s:
    case Ef.Sess{mo, st}:
      match st:
        case None{}:
          pe.void(pe.Fixed(Ef.act(a, Ef.Sess{mo, None{}})), f)
        case Some{l}:
          pe.actset_fix(a, mo, l, f)

def pe.run_fix(acts: List<&2, Ef.Act>, +s: Ef.Sess, f: pe.Fixed(s)) -> pe.Fixed(Ef.run(acts, s)):
  match acts:
    case Nil{}:
      f
    case +a <> rest:
      pe.run_fix(rest, Ef.act(a, s), pe.act_fix(s, a, f))

def pe.fix_sent(t: Ef.Sess, f: pe.Fixed(t)) -> {Ef.Sess.stored(t) == Some{Ef.sent(t)} : Maybe<&2, Ef.Lv>}:
  match t:
    case Ef.Sess{+mo, st}:
      match st:
        case None{}:
          pe.void({Ef.Sess.stored(Ef.Sess{mo, None{}}) == Some{Ef.sent(Ef.Sess{mo, None{}})} : Maybe<&2, Ef.Lv>}, f)
        case Some{+l}:
          Equal.cong(Ef.Lv, Maybe<&2, Ef.Lv>, v => Some{v}, l, Ef.fit(mo, l), Equal.sym(Ef.Lv, Ef.fit(mo, l), l, f))

def pe.fix_shown(t: Ef.Sess, f: pe.Fixed(t)) -> {Ef.shown(t) == Ef.Level{Ef.sent(t)} : Ef.Shown}:
  match t:
    case Ef.Sess{+mo, st}:
      match st:
        case None{}:
          pe.void({Ef.shown(Ef.Sess{mo, None{}}) == Ef.Level{Ef.sent(Ef.Sess{mo, None{}})} : Ef.Shown}, f)
        case Some{+l}:
          {==}

# The laws
# --------

def pe.effort_offered_plain(+map: Ef.LvMap) -> {Ef.offered(Ef.Mdl{False{}, map}) == [Ef.Off{}] : List<&2, Ef.Lv>}:
  {==}

def pe.effort_offered_null(+map: Ef.LvMap, +l: Ef.Lv, null: {Ef.entry(l, map) == Ef.Null{} : Ef.Ent}) -> {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == False{} : Bool}:
  +ladder = Ef.ladder()
  +nk = Equal.cong(Ef.Ent, Bool, e => Ef.keep.e(l, e), Ef.entry(l, map), Ef.Null{}, null)
  pe.offer_out(map, ladder, l, pe.kat(map, ladder), {==}, Ef.at(ladder, l), {==}, nk)

def pe.effort_offered_ext(r: Bool, +map: Ef.LvMap, +l: Ef.Lv, x: {Ef.ext(l) == True{} : Bool}, in: {Ef.has(Ef.offered(Ef.Mdl{r, map}), l) == True{} : Bool}) -> {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}:
  match r:
    case True{}:
      pe.wire(l, Ef.entry(l, map), x, pe.offer_in(map, Ef.ladder(), l, in))
    case False{}:
      +same = Equal.cong(Ef.Lv, Bool, v => Ef.ext(v), Ef.Off{}, l, pe.lv_true(Ef.Off{}, l, pe.or_false_t(Ef.Lv.eq(Ef.Off{}, l), in)))
      pe.absurdF({Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}, Equal.trans(Bool, False{}, Ef.ext(l), True{}, same, x))

def pe.effort_offered_kept(+map: Ef.LvMap, +l: Ef.Lv, k: {Ef.keep(map, l) == True{} : Bool}) -> {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == True{} : Bool}:
  +ladder = Ef.ladder()
  pe.offer_keep(map, ladder, l, pe.kat(map, ladder), {==}, Ef.at(ladder, l), {==}, k, pe.on_ladder(l))

def pe.effort_offered_asc(m: Ef.Mdl) -> {Ef.asc(Ef.offered(m)) == True{} : Bool}:
  match m:
    case Ef.Mdl{r, +map}:
      match r:
        case True{}:
          pe.offer_asc(map, Ef.ladder(), pe.kat(map, Ef.ladder()), {==}, {==})
        case False{}:
          {==}

def pe.effort_clamp_offered(+m: Ef.Mdl, +l: Ef.Lv, ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}) -> {Ef.has(Ef.offered(m), Ef.clamp(m, l)) == True{} : Bool}:
  pe.clamp_in(Ef.offered(m), l, ne)

def pe.effort_clamp_keeps(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.clamp(m, l) == l : Ef.Lv}:
  pe.clamp_keep(Ef.offered(m), l, in)

def pe.effort_clamp_idem(+m: Ef.Mdl, +l: Ef.Lv) -> {Ef.clamp(m, Ef.clamp(m, l)) == Ef.clamp(m, l) : Ef.Lv}:
  pe.clamp_idem(Ef.offered(m), l)

def pe.effort_cycle_still(+m: Ef.Mdl, +l: Ef.Lv, +d: Ef.Dir, few: {Ef.two(Ef.offered(m)) == False{} : Bool}) -> {Ef.cycle(m, l, d) == None{} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(Bool, Ef.two(Ef.offered(m)), False{}, few) : {Ef.cycle.at(_, Ef.offered(m), l, d) == None{} : Maybe<&2, Ef.Lv>}
  {==}

def pe.effort_cycle_next(+m: Ef.Mdl, +pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split) : {Ef.cycle.in(_, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}
  pe.next(pre, a, b, post, pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split, pe.effort_offered_asc(m)))

def pe.effort_cycle_wrap(+m: Ef.Mdl, +h: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split) : {Ef.cycle.in(_, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}
  pe.wrap(h, pre, z, pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split, pe.effort_offered_asc(m)))

def pe.effort_cycle_prev(+m: Ef.Mdl, +pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split) : {Ef.cycle.in(_, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}
  pe.prev(pre, a, b, post, pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split, pe.effort_offered_asc(m)))

def pe.effort_cycle_wrap_back(+m: Ef.Mdl, +h: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv, split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split) : {Ef.cycle.in(_, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}
  pe.wrap_back(h, pre, z)

def pe.effort_cycle_inverse(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.turn(m, Ef.turn(m, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  pe.bf_any(Ef.offered(m), l, pe.effort_offered_asc(m), in)

def pe.effort_cycle_inverse_back(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.turn(m, Ef.turn(m, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  pe.fb_any(Ef.offered(m), l, pe.effort_offered_asc(m), in)

def pe.effort_unset_default(+mo: Maybe<&2, Ef.Mdl>) -> {Ef.shown(Ef.Sess{mo, None{}}) == Ef.Default{} : Ef.Shown}:
  {==}

def pe.effort_settle_offered(+m: Ef.Mdl, +st: Maybe<&2, Ef.Lv>, +dflt: Ef.Lv, +k: Ef.Lv, ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}, settled: {Ef.Sess.stored(Ef.open(Ef.Sess{Some{m}, st}, dflt)) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(Ef.offered(m), k) == True{} : Bool}:
  +x = Maybe.default(&2, Ef.Lv, st, dflt)
  +e = Equal.cong(Maybe<&2, Ef.Lv>, Ef.Lv, v => Maybe.default(&2, Ef.Lv, v, Ef.Off{}), Some{Ef.clamp(m, x)}, Some{k}, settled)
  %e : {Ef.has(Ef.offered(m), _) == True{} : Bool}
  pe.clamp_in(Ef.offered(m), x, ne)

def pe.effort_stored_is_sent(+s: Ef.Sess, +dflt: Ef.Lv, +acts: List<&2, Ef.Act>) -> {Ef.Sess.stored(Ef.run(acts, Ef.open(s, dflt))) == Some{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Maybe<&2, Ef.Lv>}:
  pe.fix_sent(Ef.run(acts, Ef.open(s, dflt)), pe.run_fix(acts, Ef.open(s, dflt), pe.open_fix(s, dflt)))

def pe.effort_shown_is_sent(+s: Ef.Sess, +dflt: Ef.Lv, +acts: List<&2, Ef.Act>) -> {Ef.shown(Ef.run(acts, Ef.open(s, dflt))) == Ef.Level{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Ef.Shown}:
  pe.fix_shown(Ef.run(acts, Ef.open(s, dflt)), pe.run_fix(acts, Ef.open(s, dflt), pe.open_fix(s, dflt)))
