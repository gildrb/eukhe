# eukhe: lemmas of LAW metric_print_round_trip: the printed digits of a
# canonical decimal, and what the parser's canonical step makes of them

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../spec/autoresearch/decimal.bend as SD
import ../../../spec/autoresearch/metric_line.bend as SL
import ../base/dec.bend as AdDec

# Arithmetic
# ----------

def ad.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : AdDec.ad.BD(_, Unit, A)
  Unit{}

def ad.not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      AdDec.ad.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ad.sub_zero(s: Nat) -> {Nat.sub(s, 0n) == s : Nat}:
  match s:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ad.sub_add_l(r: Nat, +s: Nat) -> {Nat.sub(Nat.add(r, s), r) == s : Nat}:
  match r:
    case 0n:
      ad.sub_zero(s)
    case 1n+q:
      ad.sub_add_l(q, s)

# sc at most n: n - sc, then sc, is n
def ad.le_split(n: Nat, sc: Nat, h: {Nat.is_le(sc, n) == True{} : Bool}) -> {Nat.add(Nat.sub(n, sc), sc) == n : Nat}:
  match n sc:
    case 0n 0n:
      {==}
    case 1n+m 0n:
      AdDec.ad.add_zero(1n+m)
    case 0n 1n+s:
      AdDec.ad.absurd({Nat.add(0n, 1n+s) == 0n : Nat}, h)
    case 1n++m 1n++s:
      Equal.trans(Nat, Nat.add(Nat.sub(m, s), 1n+s), 1n+Nat.add(Nat.sub(m, s), s), 1n+m,
        AdDec.ad.add_succ(Nat.sub(m, s), s),
        Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.sub(m, s), s), m, ad.le_split(m, s, h)))

def ad.sub_sub(+n: Nat, +sc: Nat, h: {Nat.is_le(sc, n) == True{} : Bool}) -> {Nat.sub(n, Nat.sub(n, sc)) == sc : Nat}:
  %ad.le_split(n, sc, h) : {Nat.sub(_, Nat.sub(n, sc)) == sc : Nat}
  ad.sub_add_l(Nat.sub(n, sc), sc)

def ad.le0(q: Nat) -> {Nat.is_le(0n, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def ad.lt_succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      AdDec.ad.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      ad.le0(q)
    case 1n+p 0n:
      AdDec.ad.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ad.lt_succ_le(p, q, h)

# sc below n: n - sc is a successor
def ad.lt_sub(sc: Nat, n: Nat, h: {Nat.is_lt(sc, n) == True{} : Bool}) -> {Nat.sub(n, sc) == 1n+Nat.sub(n, 1n+sc) : Nat}:
  match sc n:
    case 0n 0n:
      AdDec.ad.absurd({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, h)
    case 0n 1n++m:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, ad.sub_zero(m)) : {1n+m == 1n+_ : Nat}
      {==}
    case 1n+s 0n:
      AdDec.ad.absurd({Nat.sub(0n, 1n+s) == 1n+Nat.sub(0n, 2n+s) : Nat}, h)
    case 1n+s 1n+m:
      ad.lt_sub(s, m, h)

def ad.not_lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ad.absurd_tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ad.not_lt_le(p, q, h)

# Digit lists
# -----------

# the first k digits, and the rest
def ad.take(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case x <> t:
          x <> ad.take(p, t)

def ad.skip(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case x <> t:
          ad.skip(p, t)

def ad.split_eq(k: Nat, xs: List<&2, Nat>) -> {(ad.take(k, xs), ad.skip(k, xs)) == ArD.split(k, xs) : List<&2, Nat> & List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> +t:
          %ad.split_eq(p, t) : {(x <> ad.take(p, t), ad.skip(p, t)) == ArD.split.on(x, _) : List<&2, Nat> & List<&2, Nat>}
          {==}

def ad.cat_take_skip(k: Nat, xs: List<&2, Nat>) -> {ArD.cat(ad.take(k, xs), ad.skip(k, xs)) == xs : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case +x <> +t:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, l => x <> l, ArD.cat(ad.take(p, t), ad.skip(p, t)), t, ad.cat_take_skip(p, t))

def ad.len_skip(k: Nat, xs: List<&2, Nat>) -> {ArD.len(ad.skip(k, xs)) == Nat.sub(ArD.len(xs), k) : Nat}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n x <> t:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p x <> t:
      ad.len_skip(p, t)

def ad.digits_take(k: Nat, xs: List<&2, Nat>, +h: {SD.digits_ok(xs) == True{} : Bool}) -> {SD.digits_ok(ad.take(k, xs)) == True{} : Bool}:
  match k xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p +x <> +t:
      AdDec.ad.and_intro(Nat.is_lt(x, 10n), SD.digits_ok(ad.take(p, t)), AdDec.ad.and_l(Nat.is_lt(x, 10n), SD.digits_ok(t), h), ad.digits_take(p, t, AdDec.ad.and_r(Nat.is_lt(x, 10n), SD.digits_ok(t), h)))

def ad.digits_skip(k: Nat, xs: List<&2, Nat>, h: {SD.digits_ok(xs) == True{} : Bool}) -> {SD.digits_ok(ad.skip(k, xs)) == True{} : Bool}:
  match k xs:
    case 0n _:
      h
    case 1n+p Nil{}:
      {==}
    case 1n+p +x <> +t:
      ad.digits_skip(p, t, AdDec.ad.and_r(Nat.is_lt(x, 10n), SD.digits_ok(t), h))

def ad.any_len(xs: List<&2, Nat>) -> {ArL.any_d(xs) == Nat.is_lt(0n, ArD.len(xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def ad.any_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>, h: {ArL.any_d(ys) == True{} : Bool}) -> {ArL.any_d(ArD.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> t:
      {==}

def ad.cat_nil(xs: List<&2, Nat>) -> {ArD.cat(xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => x <> l, ArD.cat(t, Nil{}), t, ad.cat_nil(t))

def ad.dlen_len(xs: List<&2, Nat>) -> {SL.dlen(xs) == ArD.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(Nat, Nat, k => 1n+k, SL.dlen(t), ArD.len(t), ad.dlen_len(t))

def ad.put_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>, -r: String) -> {ArD.put_ds(ArD.cat(xs, ys), r) == ArD.put_ds(xs, ArD.put_ds(ys, r)) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(String, String, s => SCon{ArD.dchar(x), s}, ArD.put_ds(ArD.cat(t, ys), r), ArD.put_ds(t, ArD.put_ds(ys, r)), ad.put_cat(t, ys, r))

# The last digit
# --------------

def ad.last_cons(x: Nat, ws: List<&2, Nat>, h: {ArL.any_d(ws) == True{} : Bool}) -> {SD.last_nz(x <> ws) == SD.last_nz(ws) : Bool}:
  match ws:
    case Nil{}:
      AdDec.ad.absurd({SD.last_nz([x]) == SD.last_nz(Nil{}) : Bool}, h)
    case w <> u:
      {==}

# a non-empty end keeps its last digit
def ad.last_cat(xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {ArL.any_d(ys) == True{} : Bool}) -> {SD.last_nz(ArD.cat(xs, ys)) == SD.last_nz(ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.trans(Bool, SD.last_nz(x <> ArD.cat(t, ys)), SD.last_nz(ArD.cat(t, ys)), SD.last_nz(ys),
        ad.last_cons(x, ArD.cat(t, ys), ad.any_cat(t, ys, h)),
        ad.last_cat(t, ys, h))

def ad.strip_keep(t: List<&2, Nat>, +x: Nat, h: {SD.last_nz(x <> t) == True{} : Bool}) -> {ArL.strip(x <> t) == x <> t : List<&2, Nat>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(x, 0n), False{}, ad.not_true(Nat.is_eq(x, 0n), h)) : {ArL.strip.last(_, x) == [x] : List<&2, Nat>}
      {==}
    case +e <> +u:
      %Equal.sym(List<&2, Nat>, ArL.strip(e <> u), e <> u, ad.strip_keep(u, e, h)) : {ArL.strip.at(x, _) == x <> (e <> u) : List<&2, Nat>}
      {==}

# digits whose last is not 0 strip to themselves
def ad.strip_id(xs: List<&2, Nat>, h: {SD.last_nz(xs) == True{} : Bool}) -> {ArL.strip(xs) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      AdDec.ad.absurd({ArL.strip(Nil{}) == Nil{} : List<&2, Nat>}, h)
    case x <> t:
      ad.strip_keep(t, x, h)

# Leading zeros
# -------------

def ad.drop_nz(+h: Nat, +t: List<&2, Nat>, hz: {Nat.is_eq(h, 0n) == False{} : Bool}) -> {ArL.drop(h <> t) == h <> t : List<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(h, 0n), False{}, hz) : {ArL.drop.at(_, h, t, ArL.drop(t)) == h <> t : List<&2, Nat>}
  {==}

def ad.drop_zeros(k: Nat, -xs: List<&2, Nat>) -> {ArL.drop(ArD.cat(ArD.zeros(k), xs)) == ArL.drop(xs) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      ad.drop_zeros(j, xs)

# Chars
# -----

# the char of a digit is no '-'
def ad.dchar_minus(h: Nat, hh: {Nat.is_lt(h, 10n) == True{} : Bool}) -> {ArL.same_char(ArD.dchar(h), '-') == False{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n+h1:
      match h1:
        case 0n:
          {==}
        case 1n+h2:
          match h2:
            case 0n:
              {==}
            case 1n+h3:
              match h3:
                case 0n:
                  {==}
                case 1n+h4:
                  match h4:
                    case 0n:
                      {==}
                    case 1n+h5:
                      match h5:
                        case 0n:
                          {==}
                        case 1n+h6:
                          match h6:
                            case 0n:
                              {==}
                            case 1n+h7:
                              match h7:
                                case 0n:
                                  {==}
                                case 1n+h8:
                                  match h8:
                                    case 0n:
                                      {==}
                                    case 1n+h9:
                                      match h9:
                                        case 0n:
                                          {==}
                                        case 1n+h10:
                                          match h10:
                                            case 0n:
                                              AdDec.ad.absurd({ArL.same_char(ArD.dchar(10n), '-') == False{} : Bool}, hh)
                                            case 1n+h11:
                                              AdDec.ad.absurd({ArL.same_char(ArD.dchar(11n+h11), '-') == False{} : Bool}, hh)

# The canonical step
# ------------------

def ad.canon_go(+name: String, +neg: Bool, -int: List<&2, Nat>, -f: List<&2, Nat>, +h: Nat, +t: List<&2, Nat>, +sc: Nat, ed: {ArL.drop(ArD.cat(int, f)) == h <> t : List<&2, Nat>}, el: {ArD.len(f) == sc : Nat}, fit: {Nat.is_le(ArD.len(h <> t), 15n) == True{} : Bool}) -> {ArL.canon.go(name, neg, int, f) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, sc}}} : Maybe<&2, ArL.Kv>}:
  %Equal.sym(List<&2, Nat>, ArL.drop(ArD.cat(int, f)), h <> t, ed) : {ArL.canon.fit(Nat.is_le(ArD.len(_), 15n), name, neg, _, ArD.len(f)) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, sc}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Nat, ArD.len(f), sc, el) : {ArL.canon.fit(Nat.is_le(ArD.len(h <> t), 15n), name, neg, h <> t, _) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, sc}}} : Maybe<&2, ArL.Kv>}
  %Equal.sym(Bool, Nat.is_le(ArD.len(h <> t), 15n), True{}, fit) : {ArL.canon.fit(_, name, neg, h <> t, sc) == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, sc}}} : Maybe<&2, ArL.Kv>}
  %AdDec.ad.and_true(neg) : {Some{ArL.Kv{name, ArD.Dec{_, h <> t, sc}}} == Some{ArL.Kv{name, ArD.Dec{neg, h <> t, sc}}} : Maybe<&2, ArL.Kv>}
  {==}
