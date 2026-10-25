# eukhe: lemmas of the desk's safety proofs about its callers: their
# numbers (each held once, below the next one's), who is live after a
# cut, a set, an unwait or a wake, and who a wake names.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../base/staging.bend as LStaging
import ../../../laws/auth_flight/safety.bend as SS
import ./entry.bend as LAE
import ./logic.bend as AL

# Caller numbers
# --------------
# Every live caller's number is below the next one's (ad.below), and the
# numbers fall from the newest to the oldest (ad.desc): each number is
# held once.

def ad.below(+m: Nat, cs: List<&2, F.Cl>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case F.Cl{j, p, a}:
          Bool.and(Nat.is_lt(j, m), ad.below(m, t))

def ad.desc(cs: List<&2, F.Cl>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case x <> +t:
      match x:
        case F.Cl{j, p, a}:
          Bool.and(ad.below(j, t), ad.desc(t))

def ad.below_succ(+m: Nat, cs: List<&2, F.Cl>, h: {ad.below(m, cs) == True{} : Bool}) -> {ad.below(1n+m, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, p, a}:
          +h2 = h
          AL.ad.and_tt(Nat.is_lt(j, 1n+m), ad.below(1n+m, t), AL.ad.lt_succ(j, m, AL.ad.and_l(Nat.is_lt(j, m), ad.below(m, t), h2)), ad.below_succ(m, t, AL.ad.and_r(Nat.is_lt(j, m), ad.below(m, t), h2)))

def ad.below_set_at(hit: Bool, +j: Nat, +p: String, o: F.At, +a: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +m: Nat, ih: {ad.below(m, r) == ad.below(m, t) : Bool}) -> {ad.below(m, S.af_set.pick(hit, F.Cl{j, p, o}, a, t, r)) == Bool.and(Nat.is_lt(j, m), ad.below(m, t)) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      %ih : {Bool.and(Nat.is_lt(j, m), ad.below(m, r)) == Bool.and(Nat.is_lt(j, m), _) : Bool}
      {==}

# a set keeps the numbers
def ad.below_set(+m: Nat, +k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> {ad.below(m, S.af_set(k, a, cs)) == ad.below(m, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          ad.below_set_at(Nat.is_eq(j, k), j, p, o, a, t, S.af_set(k, a, t), m, ad.below_set(m, k, a, t))

def ad.desc_set_at(hit: Bool, +j: Nat, +p: String, o: F.At, +a: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, eb: {ad.below(j, r) == ad.below(j, t) : Bool}, ih: {ad.desc(r) == ad.desc(t) : Bool}) -> {ad.desc(S.af_set.pick(hit, F.Cl{j, p, o}, a, t, r)) == Bool.and(ad.below(j, t), ad.desc(t)) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      %eb : {Bool.and(ad.below(j, r), ad.desc(r)) == Bool.and(_, ad.desc(t)) : Bool}
      %ih : {Bool.and(ad.below(j, r), ad.desc(r)) == Bool.and(ad.below(j, r), _) : Bool}
      {==}

def ad.desc_set(+k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> {ad.desc(S.af_set(k, a, cs)) == ad.desc(cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          ad.desc_set_at(Nat.is_eq(j, k), j, p, o, a, t, S.af_set(k, a, t), ad.below_set(j, k, a, t), ad.desc_set(k, a, t))

def ad.below_cut_at(hit: Bool, +j: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +m: Nat, hj: {Nat.is_lt(j, m) == True{} : Bool}, ht: {ad.below(m, t) == True{} : Bool}, ih: {ad.below(m, r) == True{} : Bool}) -> {ad.below(m, S.af_cut.pick(hit, F.Cl{j, p, o}, t, r)) == True{} : Bool}:
  match hit:
    case True{}:
      ht
    case False{}:
      AL.ad.and_tt(Nat.is_lt(j, m), ad.below(m, r), hj, ih)

# a cut keeps every number below m
def ad.below_cut(+m: Nat, +k: Nat, cs: List<&2, F.Cl>, h: {ad.below(m, cs) == True{} : Bool}) -> {ad.below(m, S.af_cut(k, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          +h2 = h
          +ht = AL.ad.and_r(Nat.is_lt(j, m), ad.below(m, t), h2)
          ad.below_cut_at(Nat.is_eq(j, k), j, p, o, t, S.af_cut(k, t), m, AL.ad.and_l(Nat.is_lt(j, m), ad.below(m, t), h2), ht, ad.below_cut(m, k, t, ht))

def ad.desc_cut_at(hit: Bool, +j: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, ht: {ad.desc(t) == True{} : Bool}, hb: {ad.below(j, r) == True{} : Bool}, ih: {ad.desc(r) == True{} : Bool}) -> {ad.desc(S.af_cut.pick(hit, F.Cl{j, p, o}, t, r)) == True{} : Bool}:
  match hit:
    case True{}:
      ht
    case False{}:
      AL.ad.and_tt(ad.below(j, r), ad.desc(r), hb, ih)

def ad.desc_cut(+k: Nat, cs: List<&2, F.Cl>, h: {ad.desc(cs) == True{} : Bool}) -> {ad.desc(S.af_cut(k, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          +h2 = h
          +ht = AL.ad.and_r(ad.below(j, t), ad.desc(t), h2)
          ad.desc_cut_at(Nat.is_eq(j, k), j, p, o, t, S.af_cut(k, t), ht, ad.below_cut(j, k, t, AL.ad.and_l(ad.below(j, t), ad.desc(t), h2)), ad.desc_cut(k, t, ht))

def ad.below_unwait_at(hit: Bool, +j: Nat, +q: String, +o: F.At, +r: List<&2, F.Cl>, +m: Nat, hj: {Nat.is_lt(j, m) == True{} : Bool}, ih: {ad.below(m, r) == True{} : Bool}) -> {ad.below(m, S.af_unwait.pick(hit, F.Cl{j, q, o}, r)) == True{} : Bool}:
  match hit:
    case True{}:
      ih
    case False{}:
      AL.ad.and_tt(Nat.is_lt(j, m), ad.below(m, r), hj, ih)

def ad.below_unwait(+m: Nat, +p: String, cs: List<&2, F.Cl>, h: {ad.below(m, cs) == True{} : Bool}) -> {ad.below(m, S.af_unwait(p, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +o}:
          +h2 = h
          ad.below_unwait_at(S.af_waits(p, F.Cl{j, q, o}), j, q, o, S.af_unwait(p, t), m, AL.ad.and_l(Nat.is_lt(j, m), ad.below(m, t), h2), ad.below_unwait(m, p, t, AL.ad.and_r(Nat.is_lt(j, m), ad.below(m, t), h2)))

def ad.desc_unwait_at(hit: Bool, +j: Nat, +q: String, +o: F.At, +r: List<&2, F.Cl>, hb: {ad.below(j, r) == True{} : Bool}, ih: {ad.desc(r) == True{} : Bool}) -> {ad.desc(S.af_unwait.pick(hit, F.Cl{j, q, o}, r)) == True{} : Bool}:
  match hit:
    case True{}:
      ih
    case False{}:
      AL.ad.and_tt(ad.below(j, r), ad.desc(r), hb, ih)

def ad.desc_unwait(+p: String, cs: List<&2, F.Cl>, h: {ad.desc(cs) == True{} : Bool}) -> {ad.desc(S.af_unwait(p, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +o}:
          +h2 = h
          ad.desc_unwait_at(S.af_waits(p, F.Cl{j, q, o}), j, q, o, S.af_unwait(p, t), ad.below_unwait(j, p, t, AL.ad.and_l(ad.below(j, t), ad.desc(t), h2)), ad.desc_unwait(p, t, AL.ad.and_r(ad.below(j, t), ad.desc(t), h2)))

# Who is live
# -----------

# a caller numbered below every live number is not live
def ad.lt_ne2(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LAE.ae.ft({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ad.lt_ne2(p, q, h)

def ad.below_dead(+k: Nat, cs: List<&2, F.Cl>, h: {ad.below(k, cs) == True{} : Bool}) -> {SS.af_live(k, cs) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, p, a}:
          +h2 = h
          %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ad.lt_ne2(j, k, AL.ad.and_l(Nat.is_lt(j, k), ad.below(k, t), h2))) : {Bool.or(_, SS.af_live(k, t)) == False{} : Bool}
          ad.below_dead(k, t, AL.ad.and_r(Nat.is_lt(j, k), ad.below(k, t), h2))

# from b || x with b false, x
def ad.or_false(+b: Bool, +x: Bool, eb: {b == False{} : Bool}, h: {Bool.or(b, x) == True{} : Bool}) -> {x == True{} : Bool}:
  match b:
    case True{}:
      LAE.ae.tf({x == True{} : Bool}, eb)
    case False{}:
      h

def ad.live_below_at(v: Bool, +j: Nat, +k: Nat, +m: Nat, +t: List<&2, F.Cl>, +ev: {Nat.is_eq(j, k) == v : Bool}, hb: {Bool.and(Nat.is_lt(j, m), ad.below(m, t)) == True{} : Bool}, hl: {Bool.or(Nat.is_eq(j, k), SS.af_live(k, t)) == True{} : Bool}, ih: {SS.af_live(k, t) == True{} : Bool} -> {Nat.is_lt(k, m) == True{} : Bool}) -> {Nat.is_lt(k, m) == True{} : Bool}:
  match v:
    case True{}:
      +e = AL.ad.eq_true(j, k, ev)
      %e : {Nat.is_lt(_, m) == True{} : Bool}
      AL.ad.and_l(Nat.is_lt(j, m), ad.below(m, t), hb)
    case False{}:
      ih(ad.or_false(Nat.is_eq(j, k), SS.af_live(k, t), ev, hl))

# a live caller's number is below the next one's
def ad.live_below(+k: Nat, +m: Nat, cs: List<&2, F.Cl>, hb: {ad.below(m, cs) == True{} : Bool}, hl: {SS.af_live(k, cs) == True{} : Bool}) -> {Nat.is_lt(k, m) == True{} : Bool}:
  match cs:
    case Nil{}:
      LAE.ae.ft({Nat.is_lt(k, m) == True{} : Bool}, hl)
    case x <> +t:
      match x:
        case F.Cl{+j, p, a}:
          +hb2 = hb
          ad.live_below_at(Nat.is_eq(j, k), j, k, m, t, {==}, hb2, hl, h => ad.live_below(k, m, t, AL.ad.and_r(Nat.is_lt(j, m), ad.below(m, t), hb2), h))

# from b || x false, b false; and x false
def ad.nor_l(+b: Bool, +x: Bool, h: {Bool.or(b, x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def ad.nor_r(+b: Bool, +x: Bool, h: {Bool.or(b, x) == False{} : Bool}) -> {x == False{} : Bool}:
  match b:
    case True{}:
      LAE.ae.tf({x == False{} : Bool}, h)
    case False{}:
      h

def ad.nor_ff(+b: Bool, +x: Bool, hb: {b == False{} : Bool}, hx: {x == False{} : Bool}) -> {Bool.or(b, x) == False{} : Bool}:
  %Equal.sym(Bool, b, False{}, hb) : {Bool.or(_, x) == False{} : Bool}
  hx

def ad.or_true_r(+b: Bool, +x: Bool, h: {x == True{} : Bool}) -> {Bool.or(b, x) == True{} : Bool}:
  AL.ad.or_r(b, x, h)

# The found caller
# ----------------

def ad.j_of(m: Maybe<&2, F.Cl>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          j

def ad.p_of(m: Maybe<&2, F.Cl>) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          p

def ad.at_of(m: Maybe<&2, F.Cl>) -> F.At:
  match m:
    case None{}:
      F.Loads{}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          a

# the caller a find hit is the one found
def ad.hit_j(-j0: Nat, -p0: String, -o0: F.At, -j: Nat, -p: String, -o: F.At, at: {Some{F.Cl{j0, p0, o0}} == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}) -> {j0 == j : Nat}:
  Equal.cong(Maybe<&2, F.Cl>, Nat, m => ad.j_of(m), Some{F.Cl{j0, p0, o0}}, Some{F.Cl{j, p, o}}, at)

def ad.hit_p(-j0: Nat, -p0: String, -o0: F.At, -j: Nat, -p: String, -o: F.At, at: {Some{F.Cl{j0, p0, o0}} == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}) -> {p0 == p : String}:
  Equal.cong(Maybe<&2, F.Cl>, String, m => ad.p_of(m), Some{F.Cl{j0, p0, o0}}, Some{F.Cl{j, p, o}}, at)

def ad.hit_o(-j0: Nat, -p0: String, -o0: F.At, -j: Nat, -p: String, -o: F.At, at: {Some{F.Cl{j0, p0, o0}} == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}) -> {o0 == o : F.At}:
  Equal.cong(Maybe<&2, F.Cl>, F.At, m => ad.at_of(m), Some{F.Cl{j0, p0, o0}}, Some{F.Cl{j, p, o}}, at)

def ad.find_live_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +k: Nat, +t: List<&2, F.Cl>, -x: F.Cl, +ev: {Nat.is_eq(j0, k) == v : Bool}, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{x} : Maybe<&2, F.Cl>}, ih: {S.af_find(k, t) == Some{x} : Maybe<&2, F.Cl>} -> {SS.af_live(k, t) == True{} : Bool}) -> {Bool.or(Nat.is_eq(j0, k), SS.af_live(k, t)) == True{} : Bool}:
  match v:
    case True{}:
      AL.ad.or_l(Nat.is_eq(j0, k), SS.af_live(k, t), ev)
    case False{}:
      AL.ad.or_r(Nat.is_eq(j0, k), SS.af_live(k, t), ih(at))

# a caller found is live
def ad.find_live(+k: Nat, cs: List<&2, F.Cl>, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}) -> {SS.af_live(k, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      LAE.ae.none_some(F.Cl, {SS.af_live(k, Nil{}) == True{} : Bool}, x, at)
    case y <> +t:
      match y:
        case F.Cl{+j0, +p0, +o0}:
          ad.find_live_at(Nat.is_eq(j0, k), j0, p0, o0, k, t, x, {==}, at, h => ad.find_live(k, t, x, h))

def ad.live_set_at(hit: Bool, +j0: Nat, +p: String, o: F.At, +a: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +j: Nat, ih: {SS.af_live(j, r) == SS.af_live(j, t) : Bool}) -> {SS.af_live(j, S.af_set.pick(hit, F.Cl{j0, p, o}, a, t, r)) == Bool.or(Nat.is_eq(j0, j), SS.af_live(j, t)) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      %ih : {Bool.or(Nat.is_eq(j0, j), SS.af_live(j, r)) == Bool.or(Nat.is_eq(j0, j), _) : Bool}
      {==}

# a set keeps who is live
def ad.live_set(+j: Nat, +k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> {SS.af_live(j, S.af_set(k, a, cs)) == SS.af_live(j, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p, +o}:
          ad.live_set_at(Nat.is_eq(j0, k), j0, p, o, a, t, S.af_set(k, a, t), j, ad.live_set(j, k, a, t))

def ad.dead_cut_at(hit: Bool, +j0: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +j: Nat, hj: {Nat.is_eq(j0, j) == False{} : Bool}, ht: {SS.af_live(j, t) == False{} : Bool}, ih: {SS.af_live(j, r) == False{} : Bool}) -> {SS.af_live(j, S.af_cut.pick(hit, F.Cl{j0, p, o}, t, r)) == False{} : Bool}:
  match hit:
    case True{}:
      ht
    case False{}:
      ad.nor_ff(Nat.is_eq(j0, j), SS.af_live(j, r), hj, ih)

# a caller not live is not live after a cut
def ad.dead_cut(+j: Nat, +k: Nat, cs: List<&2, F.Cl>, h: {SS.af_live(j, cs) == False{} : Bool}) -> {SS.af_live(j, S.af_cut(k, cs)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p, +o}:
          +h2 = h
          +ht = ad.nor_r(Nat.is_eq(j0, j), SS.af_live(j, t), h2)
          ad.dead_cut_at(Nat.is_eq(j0, k), j0, p, o, t, S.af_cut(k, t), j, ad.nor_l(Nat.is_eq(j0, j), SS.af_live(j, t), h2), ht, ad.dead_cut(j, k, t, ht))

def ad.dead_unwait_at(hit: Bool, +j0: Nat, +q: String, +o: F.At, +r: List<&2, F.Cl>, +j: Nat, hj: {Nat.is_eq(j0, j) == False{} : Bool}, ih: {SS.af_live(j, r) == False{} : Bool}) -> {SS.af_live(j, S.af_unwait.pick(hit, F.Cl{j0, q, o}, r)) == False{} : Bool}:
  match hit:
    case True{}:
      ih
    case False{}:
      ad.nor_ff(Nat.is_eq(j0, j), SS.af_live(j, r), hj, ih)

# a caller not live is not live after an unwait
def ad.dead_unwait(+j: Nat, +p: String, cs: List<&2, F.Cl>, h: {SS.af_live(j, cs) == False{} : Bool}) -> {SS.af_live(j, S.af_unwait(p, cs)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +q, +o}:
          +h2 = h
          ad.dead_unwait_at(S.af_waits(p, F.Cl{j0, q, o}), j0, q, o, S.af_unwait(p, t), j, ad.nor_l(Nat.is_eq(j0, j), SS.af_live(j, t), h2), ad.dead_unwait(j, p, t, ad.nor_r(Nat.is_eq(j0, j), SS.af_live(j, t), h2)))

def ad.dead_wake_at(hit: Bool, +j0: Nat, +q: String, +o: F.At, +a: F.Act, +r: List<&2, F.To>, +j: Nat, hj: {Nat.is_eq(j0, j) == False{} : Bool}, ih: {SS.af_names_in(j, r) == 0n : Nat}) -> {SS.af_names_in(j, S.af_wake.pick(hit, F.Cl{j0, q, o}, a, r)) == 0n : Nat}:
  match hit:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j0, j), False{}, hj) : {Nat.add(S.af_bit(_), SS.af_names_in(j, r)) == 0n : Nat}
      ih
    case False{}:
      ih

# a wake names no caller that is not live
def ad.dead_wake(+j: Nat, +p: String, +a: F.Act, cs: List<&2, F.Cl>, h: {SS.af_live(j, cs) == False{} : Bool}) -> {SS.af_names_in(j, S.af_wake(p, a, cs)) == 0n : Nat}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +q, +o}:
          +h2 = h
          ad.dead_wake_at(S.af_waits(p, F.Cl{j0, q, o}), j0, q, o, a, S.af_wake(p, a, t), j, ad.nor_l(Nat.is_eq(j0, j), SS.af_live(j, t), h2), ad.dead_wake(j, p, a, t, ad.nor_r(Nat.is_eq(j0, j), SS.af_live(j, t), h2)))

def ad.gone_cut_at(v: Bool, +j0: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +k: Nat, +ev: {Nat.is_eq(j0, k) == v : Bool}, hb: {ad.below(j0, t) == True{} : Bool}, ih: {SS.af_live(k, S.af_cut(k, t)) == False{} : Bool}) -> {SS.af_live(k, S.af_cut.pick(v, F.Cl{j0, p, o}, t, S.af_cut(k, t))) == False{} : Bool}:
  match v:
    case True{}:
      +e = AL.ad.eq_true(j0, k, ev)
      ad.below_dead(k, t, Equal.trans(Bool, ad.below(k, t), ad.below(j0, t), True{}, Equal.cong(Nat, Bool, y => ad.below(y, t), k, j0, Equal.sym(Nat, j0, k, e)), hb))
    case False{}:
      ad.nor_ff(Nat.is_eq(j0, k), SS.af_live(k, S.af_cut(k, t)), ev, ih)

# with every number held once, a cut of k leaves no k
def ad.gone_cut(+k: Nat, cs: List<&2, F.Cl>, h: {ad.desc(cs) == True{} : Bool}) -> {SS.af_live(k, S.af_cut(k, cs)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p, +o}:
          +h2 = h
          ad.gone_cut_at(Nat.is_eq(j0, k), j0, p, o, t, k, {==}, AL.ad.and_l(ad.below(j0, t), ad.desc(t), h2), ad.gone_cut(k, t, AL.ad.and_r(ad.below(j0, t), ad.desc(t), h2)))

# f(a) from f(b) and a == b
def ad.tr(f: Bool -> Bool, +a: Bool, +b: Bool, e: {a == b : Bool}, h: {f(b) == True{} : Bool}) -> {f(a) == True{} : Bool}:
  Equal.trans(Bool, f(a), f(b), True{}, Equal.cong(Bool, Bool, f, a, b, e), h)

def ad.live_cut_ne_at(v: Bool, +j0: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +k: Nat, +j: Nat, +ev: {Nat.is_eq(j0, k) == v : Bool}, ne: {Nat.is_eq(k, j) == False{} : Bool}, ih: {SS.af_live(j, S.af_cut(k, t)) == SS.af_live(j, t) : Bool}) -> {SS.af_live(j, S.af_cut.pick(v, F.Cl{j0, p, o}, t, S.af_cut(k, t))) == Bool.or(Nat.is_eq(j0, j), SS.af_live(j, t)) : Bool}:
  match v:
    case True{}:
      +e = AL.ad.eq_true(j0, k, ev)
      %Equal.sym(Nat, j0, k, e) : {SS.af_live(j, t) == Bool.or(Nat.is_eq(_, j), SS.af_live(j, t)) : Bool}
      %Equal.sym(Bool, Nat.is_eq(k, j), False{}, ne) : {SS.af_live(j, t) == Bool.or(_, SS.af_live(j, t)) : Bool}
      {==}
    case False{}:
      %ih : {Bool.or(Nat.is_eq(j0, j), SS.af_live(j, S.af_cut(k, t))) == Bool.or(Nat.is_eq(j0, j), _) : Bool}
      {==}

# a cut of k keeps every other caller's liveness
def ad.live_cut_ne(+j: Nat, +k: Nat, cs: List<&2, F.Cl>, +ne: {Nat.is_eq(k, j) == False{} : Bool}) -> {SS.af_live(j, S.af_cut(k, cs)) == SS.af_live(j, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p, +o}:
          ad.live_cut_ne_at(Nat.is_eq(j0, k), j0, p, o, t, k, j, {==}, ne, ad.live_cut_ne(j, k, t, ne))

def ad.live_cut_sub_v(v: Bool, +j: Nat, +k: Nat, +cs: List<&2, F.Cl>, +ev: {SS.af_live(j, cs) == v : Bool}, h: {SS.af_live(j, S.af_cut(k, cs)) == True{} : Bool}) -> {SS.af_live(j, cs) == True{} : Bool}:
  match v:
    case True{}:
      ev
    case False{}:
      LAE.ae.tf({SS.af_live(j, cs) == True{} : Bool}, Equal.trans(Bool, True{}, SS.af_live(j, S.af_cut(k, cs)), False{}, Equal.sym(Bool, SS.af_live(j, S.af_cut(k, cs)), True{}, h), ad.dead_cut(j, k, cs, ev)))

# a caller live after a cut was live before it
def ad.live_cut_sub(+j: Nat, +k: Nat, +cs: List<&2, F.Cl>, h: {SS.af_live(j, S.af_cut(k, cs)) == True{} : Bool}) -> {SS.af_live(j, cs) == True{} : Bool}:
  ad.live_cut_sub_v(SS.af_live(j, cs), j, k, cs, {==}, h)

def ad.ends_names_at(v: Bool, +j: Nat, +a: F.Act, +t: List<&2, F.To>, +k: Nat, +ev: {Nat.is_eq(j, k) == v : Bool}, h: {Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(Nat.is_eq(j, k), SS.af_ending(a))), SS.af_ends_in(k, t))) == True{} : Bool}, ih: {Nat.is_lt(0n, SS.af_ends_in(k, t)) == True{} : Bool} -> {Nat.is_lt(0n, SS.af_names_in(k, t)) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(S.af_bit(Nat.is_eq(j, k)), SS.af_names_in(k, t))) == True{} : Bool}:
  match v:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, k), True{}, ev) : {Nat.is_lt(0n, Nat.add(S.af_bit(_), SS.af_names_in(k, t))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ev) : {Nat.is_lt(0n, Nat.add(S.af_bit(_), SS.af_names_in(k, t))) == True{} : Bool}
      ih(ad.tr(b => Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(b, SS.af_ending(a))), SS.af_ends_in(k, t))), False{}, Nat.is_eq(j, k), Equal.sym(Bool, Nat.is_eq(j, k), False{}, ev), h))

# a pair that ends k's refresh names k
def ad.ends_names(+k: Nat, xs: List<&2, F.To>, h: {Nat.is_lt(0n, SS.af_ends_in(k, xs)) == True{} : Bool}) -> {Nat.is_lt(0n, SS.af_names_in(k, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> +t:
      match x:
        case F.To{+j, +a}:
          ad.ends_names_at(Nat.is_eq(j, k), j, a, t, k, {==}, h, g => ad.ends_names(k, t, g))

def ad.live_or_ends_at(hit: Bool, v: Bool, +j0: Nat, +q: String, +o: F.At, +t: List<&2, F.Cl>, +p: String, +a: F.Act, +j: Nat, +ev: {Nat.is_eq(j0, j) == v : Bool}, ea: {SS.af_ending(a) == True{} : Bool}, h: {Bool.or(Nat.is_eq(j0, j), SS.af_live(j, t)) == True{} : Bool}, ih: {SS.af_live(j, t) == True{} : Bool} -> {Bool.or(SS.af_live(j, S.af_unwait(p, t)), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake(p, a, t)))) == True{} : Bool}) -> {Bool.or(SS.af_live(j, S.af_unwait.pick(hit, F.Cl{j0, q, o}, S.af_unwait(p, t))), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake.pick(hit, F.Cl{j0, q, o}, a, S.af_wake(p, a, t))))) == True{} : Bool}:
  match hit v:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_eq(j0, j), True{}, ev) : {Bool.or(SS.af_live(j, S.af_unwait(p, t)), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(_, SS.af_ending(a))), SS.af_ends_in(j, S.af_wake(p, a, t))))) == True{} : Bool}
      %Equal.sym(Bool, SS.af_ending(a), True{}, ea) : {Bool.or(SS.af_live(j, S.af_unwait(p, t)), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(True{}, _)), SS.af_ends_in(j, S.af_wake(p, a, t))))) == True{} : Bool}
      AL.ad.or_r(SS.af_live(j, S.af_unwait(p, t)), True{}, {==})
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(j0, j), False{}, ev) : {Bool.or(SS.af_live(j, S.af_unwait(p, t)), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(_, SS.af_ending(a))), SS.af_ends_in(j, S.af_wake(p, a, t))))) == True{} : Bool}
      ih(ad.or_false(Nat.is_eq(j0, j), SS.af_live(j, t), ev, h))
    case False{} True{}:
      AL.ad.or_l(Bool.or(Nat.is_eq(j0, j), SS.af_live(j, S.af_unwait(p, t))), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake(p, a, t))), AL.ad.or_l(Nat.is_eq(j0, j), SS.af_live(j, S.af_unwait(p, t)), ev))
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(j0, j), False{}, ev) : {Bool.or(Bool.or(_, SS.af_live(j, S.af_unwait(p, t))), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake(p, a, t)))) == True{} : Bool}
      ih(ad.or_false(Nat.is_eq(j0, j), SS.af_live(j, t), ev, h))

# a live caller stays live through an unwait, or the wake of the same
# callers ends its refresh
def ad.live_or_ends(+j: Nat, +p: String, +a: F.Act, cs: List<&2, F.Cl>, +ea: {SS.af_ending(a) == True{} : Bool}, h: {SS.af_live(j, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(j, S.af_unwait(p, cs)), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake(p, a, cs)))) == True{} : Bool}:
  match cs:
    case Nil{}:
      LAE.ae.ft({Bool.or(SS.af_live(j, S.af_unwait(p, Nil{})), Nat.is_lt(0n, SS.af_ends_in(j, S.af_wake(p, a, Nil{})))) == True{} : Bool}, h)
    case x <> +t:
      match x:
        case F.Cl{+j0, +q, +o}:
          ad.live_or_ends_at(S.af_waits(p, F.Cl{j0, q, o}), Nat.is_eq(j0, j), j0, q, o, t, p, a, j, {==}, ea, h, g => ad.live_or_ends(j, p, a, t, ea, g))

def ad.wake_once_at(hit: Bool, v: Bool, +j0: Nat, +q: String, +o: F.At, +t: List<&2, F.Cl>, +p: String, +a: F.Act, +k: Nat, +ev: {Nat.is_eq(j0, k) == v : Bool}, +hb: {ad.below(j0, t) == True{} : Bool}, named: {Nat.is_lt(0n, SS.af_names_in(k, S.af_wake.pick(hit, F.Cl{j0, q, o}, a, S.af_wake(p, a, t)))) == True{} : Bool}, ih: {Nat.is_lt(0n, SS.af_names_in(k, S.af_wake(p, a, t))) == True{} : Bool} -> ({SS.af_names_in(k, S.af_wake(p, a, t)) == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, t)) == False{} : Bool})) -> ({SS.af_names_in(k, S.af_wake.pick(hit, F.Cl{j0, q, o}, a, S.af_wake(p, a, t))) == 1n : Nat} & {SS.af_live(k, S.af_unwait.pick(hit, F.Cl{j0, q, o}, S.af_unwait(p, t))) == False{} : Bool}):
  match hit v:
    case True{} True{}:
      +e = AL.ad.eq_true(j0, k, ev)
      +dt = ad.below_dead(k, t, Equal.trans(Bool, ad.below(k, t), ad.below(j0, t), True{}, Equal.cong(Nat, Bool, y => ad.below(y, t), k, j0, Equal.sym(Nat, j0, k, e)), hb))
      +w0 = ad.dead_wake(k, p, a, t, dt)
      %Equal.sym(Bool, Nat.is_eq(j0, k), True{}, ev) : ({Nat.add(S.af_bit(_), SS.af_names_in(k, S.af_wake(p, a, t))) == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, t)) == False{} : Bool})
      %Equal.sym(Nat, SS.af_names_in(k, S.af_wake(p, a, t)), 0n, w0) : ({1n+_ == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, t)) == False{} : Bool})
      ({==}, ad.dead_unwait(k, p, t, dt))
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(j0, k), False{}, ev) : ({Nat.add(S.af_bit(_), SS.af_names_in(k, S.af_wake(p, a, t))) == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, t)) == False{} : Bool})
      ih(ad.tr(b => Nat.is_lt(0n, Nat.add(S.af_bit(b), SS.af_names_in(k, S.af_wake(p, a, t)))), False{}, Nat.is_eq(j0, k), Equal.sym(Bool, Nat.is_eq(j0, k), False{}, ev), named))
    case False{} True{}:
      +e = AL.ad.eq_true(j0, k, ev)
      +dt = ad.below_dead(k, t, Equal.trans(Bool, ad.below(k, t), ad.below(j0, t), True{}, Equal.cong(Nat, Bool, y => ad.below(y, t), k, j0, Equal.sym(Nat, j0, k, e)), hb))
      +w0 = ad.dead_wake(k, p, a, t, dt)
      LAE.ae.ft(({SS.af_names_in(k, S.af_wake(p, a, t)) == 1n : Nat} & {SS.af_live(k, F.Cl{j0, q, o} <> S.af_unwait(p, t)) == False{} : Bool}), Equal.trans(Bool, False{}, Nat.is_lt(0n, SS.af_names_in(k, S.af_wake(p, a, t))), True{}, Equal.cong(Nat, Bool, y => Nat.is_lt(0n, y), 0n, SS.af_names_in(k, S.af_wake(p, a, t)), Equal.sym(Nat, SS.af_names_in(k, S.af_wake(p, a, t)), 0n, w0)), named))
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(j0, k), False{}, ev) : ({SS.af_names_in(k, S.af_wake(p, a, t)) == 1n : Nat} & {Bool.or(_, SS.af_live(k, S.af_unwait(p, t))) == False{} : Bool})
      ih(named)

# with every number held once, a caller a wake names is named once and
# is not live after the unwait of the same callers
def ad.wake_once(+k: Nat, +p: String, +a: F.Act, cs: List<&2, F.Cl>, h: {ad.desc(cs) == True{} : Bool}, named: {Nat.is_lt(0n, SS.af_names_in(k, S.af_wake(p, a, cs))) == True{} : Bool}) -> ({SS.af_names_in(k, S.af_wake(p, a, cs)) == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, cs)) == False{} : Bool}):
  match cs:
    case Nil{}:
      LAE.ae.ft(({SS.af_names_in(k, S.af_wake(p, a, Nil{})) == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, Nil{})) == False{} : Bool}), named)
    case x <> +t:
      match x:
        case F.Cl{+j0, +q, +o}:
          +h2 = h
          ad.wake_once_at(S.af_waits(p, F.Cl{j0, q, o}), Nat.is_eq(j0, k), j0, q, o, t, p, a, k, {==}, AL.ad.and_l(ad.below(j0, t), ad.desc(t), h2), named, g => ad.wake_once(k, p, a, t, AL.ad.and_r(ad.below(j0, t), ad.desc(t), h2), g))
