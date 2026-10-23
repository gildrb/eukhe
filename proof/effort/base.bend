# eukhe: lemmas the proofs of area effort share

import Base
import ../../bend/effort.bend as Ef
import ../../bend/wire.bend as Wr
import ../../bend/ffi_effort.bend as FEf
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# ---- effort ----

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

def pq.lad_has_keep.at(+map: Ef.LvMap, +l: Ef.Lv, b: Bool, eb: {Ef.keep(map, l) == b : Bool}) -> {Ef.has(Ef.offer(map, Ef.ladder()), l) == b : Bool}:
  match b:
    case True{}:
      pe.effort_offered_kept(map, l, eb)
    case False{}:
      pe.offer_out(map, Ef.ladder(), l, pe.kat(map, Ef.ladder()), {==}, Ef.at(Ef.ladder(), l), {==}, eb)

# a level is in the offer of a map exactly when the map keeps it
def pq.lad_has_keep(+map: Ef.LvMap, +l: Ef.Lv) -> {Ef.has(Ef.offer(map, Ef.ladder()), l) == Ef.keep(map, l) : Bool}:
  pq.lad_has_keep.at(map, l, Ef.keep(map, l), {==})

# a Bool reads back (Laws.wire_bool_round_trip, turned around)
def pc.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Laws.wire_bool_round_trip(b, rest))

# (effort)
# --------

# the seq of FEf reads back a then b (the two decoders in turn)
def pc.seqFEf(~A: Data, ~B: Data, ~get: String -> Wr.Dec<B>, +a: A, +r: String, +b: B, +r2: String, d: Wr.Dec<A>,
  h1: {Wr.Got{a, r} == d : Wr.Dec<A>}, h2: {Wr.Got{b, r2} == get(r) : Wr.Dec<B>}) ->
  {Wr.Got{FEf.P2{a, b}, r2} == FEf.seq(~A, ~B, ~get, d) : Wr.Dec<FEf.P2<A, B>>}:
  %h1 : {Wr.Got{FEf.P2{a, b}, r2} == FEf.seq(~A, ~B, ~get, _) : Wr.Dec<FEf.P2<A, B>>}
  %h2 : {Wr.Got{FEf.P2{a, b}, r2} == FEf.seq.fin(~A, ~B, a, _) : Wr.Dec<FEf.P2<A, B>>}
  {==}

# a Ef.Lv reads back
def pc.e_lv(+x: Ef.Lv, +rest: String) -> {Wr.Got{x, rest} == FEf.get_lv(FEf.put_lv(x, rest)) : Wr.Dec<Ef.Lv>}:
  match x:
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

# a Ef.Ent reads back
def pc.e_ent(+x: Ef.Ent, +rest: String) -> {Wr.Got{x, rest} == FEf.get_ent(FEf.put_ent(x, rest)) : Wr.Dec<Ef.Ent>}:
  match x:
    case Ef.Missing{}:
      {==}
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# a Ef.Dir reads back
def pc.e_dir(+x: Ef.Dir, +rest: String) -> {Wr.Got{x, rest} == FEf.get_dir(FEf.put_dir(x, rest)) : Wr.Dec<Ef.Dir>}:
  match x:
    case Ef.Forward{}:
      {==}
    case Ef.Backward{}:
      {==}

# a map reads back
def pc.e_map(+m: Ef.LvMap, +rest: String) -> {Wr.Got{m, rest} == FEf.get_map(FEf.put_map(m, rest)) : Wr.Dec<Ef.LvMap>}:
  match m:
    case Ef.LvMap{+o, +mi, +lo, +me, +hi, +xh, +mx}:
      +r6 = FEf.put_ent(mx, rest)
      +r5 = FEf.put_ent(xh, r6)
      +r4 = FEf.put_ent(hi, r5)
      +r3 = FEf.put_ent(me, r4)
      +r2 = FEf.put_ent(lo, r3)
      +r1 = FEf.put_ent(mi, r2)
      +r0 = FEf.put_ent(o, r1)
      +d0 = FEf.get_ent(r0)
      +e0 = pc.e_ent(o, r1)
      +d1 = FEf.seq(~Ef.Ent, ~Ef.Ent, ~FEf.get_ent, d0)
      +e1 = pc.seqFEf(~Ef.Ent, ~Ef.Ent, ~FEf.get_ent, o, r1, mi, r2, d0, e0, pc.e_ent(mi, r2))
      +d2 = FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d1)
      +e2 = pc.seqFEf(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.P2{o, mi}, r2, lo, r3, d1, e1, pc.e_ent(lo, r3))
      +d3 = FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d2)
      +e3 = pc.seqFEf(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.P2{FEf.P2{o, mi}, lo}, r3, me, r4, d2, e2, pc.e_ent(me, r4))
      +d4 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d3)
      +e4 = pc.seqFEf(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, r4, hi, r5, d3, e3, pc.e_ent(hi, r5))
      +d5 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d4)
      +e5 = pc.seqFEf(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, r5, xh, r6, d4, e4, pc.e_ent(xh, r6))
      +d6 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d5)
      +e6 = pc.seqFEf(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, xh}, r6, mx, rest, d5, e5, pc.e_ent(mx, rest))
      %e6 : {Wr.Got{Ef.LvMap{o, mi, lo, me, hi, xh, mx}, rest} == FEf.get_map.of(_) : Wr.Dec<Ef.LvMap>}
      {==}

# a Maybe<LvMap> reads back
def pc.e_mmap(+m: Maybe<&2, Ef.LvMap>, +rest: String) -> {Wr.Got{m, rest} == FEf.get_mmap(FEf.put_mmap(m, rest)) : Wr.Dec<Maybe<&2, Ef.LvMap>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %pc.e_map(x, rest) : {Wr.Got{Some{x}, rest} == FEf.get_mmap.some(_) : Wr.Dec<Maybe<&2, Ef.LvMap>>}
      {==}

# the items of xs, then rest (Ef.Lv)
def pc.e_lv_items(xs: List<&2, Ef.Lv>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FEf.put_lv(x, pc.e_lv_items(t, rest))

def pc.e_lv_put_go(xs: List<&2, Ef.Lv>, -rest: String) ->
  {Wr.put_list.go(~Ef.Lv, ~FEf.put_lv, xs, rest) == (List.length(&2, Ef.Lv, xs), pc.e_lv_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ef.Lv, ~FEf.put_lv, t, rest), (List.length(&2, Ef.Lv, t), pc.e_lv_items(t, rest)), pc.e_lv_put_go(t, rest)) : {Wr.put_list.step(~Ef.Lv, ~FEf.put_lv, x, _) == (1n+List.length(&2, Ef.Lv, t), FEf.put_lv(x, pc.e_lv_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pc.e_lv_put(+xs: List<&2, Ef.Lv>, -rest: String) ->
  {Wr.put_list(~Ef.Lv, ~FEf.put_lv, xs, rest) == Wr.put_nat(List.length(&2, Ef.Lv, xs), pc.e_lv_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ef.Lv, ~FEf.put_lv, xs, rest), (List.length(&2, Ef.Lv, xs), pc.e_lv_items(xs, rest)), pc.e_lv_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ef.Lv, xs), pc.e_lv_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pc.e_lv_go_rt(+t: List<&2, Ef.Lv>, +x: Ef.Lv, +rest: String) ->
  {Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, List.length(&2, Ef.Lv, t), FEf.get_lv(FEf.put_lv(x, pc.e_lv_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ef.Lv>>}:
  match t:
    case Nil{}:
      %pc.e_lv(x, rest) : {Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ef.Lv>>}
      {==}
    case Con{+y, +u}:
      %pc.e_lv(x, FEf.put_lv(y, pc.e_lv_items(u, rest))) : {Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, 1n+List.length(&2, Ef.Lv, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ef.Lv>>}
      %Equal.sym(Wr.Dec<List<&2, Ef.Lv>>, Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, List.length(&2, Ef.Lv, u), FEf.get_lv(FEf.put_lv(y, pc.e_lv_items(u, rest)))), Wr.Got{y <> u, rest}, pc.e_lv_go_rt(u, y, rest)) : {Wr.get_list.cons(Ef.Lv, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ef.Lv>>}
      {==}

# a list whose length fits reads back
def pc.e_lvs(+xs: List<&2, Ef.Lv>, +rest: String, h: {Laws.wire_fits(List.length(&2, Ef.Lv, xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Ef.Lv, ~FEf.get_lv, Wr.put_list(~Ef.Lv, ~FEf.put_lv, xs, rest)) : Wr.Dec<List<&2, Ef.Lv>>}:
  match xs:
    case Nil{}:
      %L.pc.nat(0n, rest, h) : {Wr.Got{Nil{}, rest} == Wr.get_list.start(~Ef.Lv, ~FEf.get_lv, _) : Wr.Dec<List<&2, Ef.Lv>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      %Equal.sym(String, Wr.put_list(~Ef.Lv, ~FEf.put_lv, x <> t, r), Wr.put_nat(List.length(&2, Ef.Lv, x <> t), pc.e_lv_items(x <> t, r)), pc.e_lv_put(x <> t, r)) : {Wr.Got{x <> t, r} == Wr.get_list(~Ef.Lv, ~FEf.get_lv, _) : Wr.Dec<List<&2, Ef.Lv>>}
      %L.pc.nat(List.length(&2, Ef.Lv, x <> t), pc.e_lv_items(x <> t, r), h) : {Wr.Got{x <> t, r} == Wr.get_list.start(~Ef.Lv, ~FEf.get_lv, _) : Wr.Dec<List<&2, Ef.Lv>>}
      Equal.sym(Wr.Dec<List<&2, Ef.Lv>>, Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, List.length(&2, Ef.Lv, t), FEf.get_lv(FEf.put_lv(x, pc.e_lv_items(t, r)))), Wr.Got{x <> t, r}, pc.e_lv_go_rt(t, x, r))

# the facts that fit read back
def pc.e_facts(+f: FEf.Facts, +rest: String, h: {Laws.core_facts_fit(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FEf.get_facts(FEf.put_facts(f, rest)) : Wr.Dec<FEf.Facts>}:
  match f:
    case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
      +hhh = h
      +hh0 = L.wr_and_r(Laws.core_lvs_fit(reasoning), Laws.core_lvs_fit(plain), hhh)
      +r5 = FEf.put_lvs(plain, rest)
      +r4 = FEf.put_lvs(reasoning, r5)
      +r3 = FEf.put_mmap(rule, r4)
      +r2 = FEf.put_mmap(explicit, r3)
      +r1 = Wr.put_bool(by_map, r2)
      +r0 = Wr.put_bool(flag, r1)
      +d0 = Wr.get_bool(r0)
      +e0 = pc.bool(flag, r1)
      +d1 = FEf.seq(~Bool, ~Bool, ~Wr.get_bool, d0)
      +e1 = pc.seqFEf(~Bool, ~Bool, ~Wr.get_bool, flag, r1, by_map, r2, d0, e0, pc.bool(by_map, r2))
      +d2 = FEf.seq(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d1)
      +e2 = pc.seqFEf(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.P2{flag, by_map}, r2, explicit, r3, d1, e1, pc.e_mmap(explicit, r3))
      +d3 = FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d2)
      +e3 = pc.seqFEf(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.P2{FEf.P2{flag, by_map}, explicit}, r3, rule, r4, d2, e2, pc.e_mmap(rule, r4))
      +d4 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d3)
      +e4 = pc.seqFEf(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.P2{FEf.P2{FEf.P2{flag, by_map}, explicit}, rule}, r4, reasoning, r5, d3, e3, pc.e_lvs(reasoning, r5, L.wr_and_l(Laws.core_lvs_fit(reasoning), Laws.core_lvs_fit(plain), hhh)))
      +d5 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d4)
      +e5 = pc.seqFEf(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.P2{FEf.P2{FEf.P2{FEf.P2{flag, by_map}, explicit}, rule}, reasoning}, r5, plain, rest, d4, e4, pc.e_lvs(plain, rest, hh0))
      %e5 : {Wr.Got{FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}, rest} == FEf.get_facts.of(_) : Wr.Dec<FEf.Facts>}
      {==}

# a ladder request that fits reads back
def pc.e_req(+q: FEf.Req, +rest: String, h: {Laws.core_effort_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FEf.get_req(FEf.put_req(q, rest)) : Wr.Dec<FEf.Req>}:
  match q:
    case FEf.Offered{+f}:
      %pc.e_facts(f, rest, h) : {Wr.Got{FEf.Offered{f}, rest} == FEf.get_offered.of(_) : Wr.Dec<FEf.Req>}
      {==}
    case FEf.Clamp{+f, +l}:
      +hhh = h
      +r1 = FEf.put_lv(l, rest)
      +r0 = FEf.put_facts(f, r1)
      +d0 = FEf.get_facts(r0)
      +e0 = pc.e_facts(f, r1, hhh)
      +d1 = FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d0)
      +e1 = pc.seqFEf(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, f, r1, l, rest, d0, e0, pc.e_lv(l, rest))
      %e1 : {Wr.Got{FEf.Clamp{f, l}, rest} == FEf.get_clamp.of(_) : Wr.Dec<FEf.Req>}
      {==}
    case FEf.Cycle{+f, +l, +d}:
      +hhh = h
      +r2 = FEf.put_dir(d, rest)
      +r1 = FEf.put_lv(l, r2)
      +r0 = FEf.put_facts(f, r1)
      +d0 = FEf.get_facts(r0)
      +e0 = pc.e_facts(f, r1, hhh)
      +d1 = FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d0)
      +e1 = pc.seqFEf(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, f, r1, l, r2, d0, e0, pc.e_lv(l, r2))
      +d2 = FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, d1)
      +e2 = pc.seqFEf(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, FEf.P2{f, l}, r2, d, rest, d1, e1, pc.e_dir(d, rest))
      %e2 : {Wr.Got{FEf.Cycle{f, l, d}, rest} == FEf.get_cycle.of(_) : Wr.Dec<FEf.Req>}
      {==}
