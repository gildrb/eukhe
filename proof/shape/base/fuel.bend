# eukhe: the fuel of the spec's readings (laws/shape/match.bend R4): a reading
# never has more chars after it than its place (shu.pf: every place of a
# list below n keeps its readings below n), and any fuel past the chars
# after every place of a list reads the same readings (shu.fi).

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./has.bend as LH

# Logic and Nat
# -------------

def shu.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def shu.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : shu.IfF(_, G)
  Unit{}

def shu.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      shu.absurd({False{} == True{} : Bool}, h)

def shu.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      shu.absurd({b == True{} : Bool}, h)

def shu.and_t(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def shu.lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def shu.lt_succ(a: Nat, n: Nat, h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.is_lt(a, 1n+n) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match n:
        case 0n:
          shu.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
        case 1n+m:
          shu.lt_succ(p, m, h)

# one less than a count below n is below n
def shu.lt_dec(a: Nat, +n: Nat, h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.is_lt(Shape.sp_dec(a), n) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      match n:
        case 0n:
          shu.absurd({Nat.is_lt(p, 0n) == True{} : Bool}, h)
        case 1n+m:
          shu.lt_succ(p, m, h)

# a below b below g + 1: a below g
def shu.lt_lt(a: Nat, b: Nat, g: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, 1n+g) == True{} : Bool}) -> {Nat.is_lt(a, g) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          shu.absurd({Nat.is_lt(0n, g) == True{} : Bool}, h1)
        case 1n+q:
          match g:
            case 0n:
              shu.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, shu.lt_zero(q)), h2))
            case 1n+k:
              {==}
    case 1n+p:
      match b:
        case 0n:
          shu.absurd({Nat.is_lt(1n+p, g) == True{} : Bool}, h1)
        case 1n+q:
          match g:
            case 0n:
              shu.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, shu.lt_zero(q)), h2))
            case 1n+k:
              shu.lt_lt(p, q, k, h1, h2)

# Places below a count
# --------------------

# every place of xs has fewer than n chars after it
def shu.fits(+n: Nat, xs: List<&2, S.St>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(Nat.is_lt(Shape.sp_left(x), n), shu.fits(n, t))

def shu.fits_app(+n: Nat, xs: List<&2, S.St>, +ys: List<&2, S.St>, +hx: {shu.fits(n, xs) == True{} : Bool}, hy: {shu.fits(n, ys) == True{} : Bool}) -> {shu.fits(n, List.append(&2, S.St, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case x <> +t:
      +a = {Nat.is_lt(Shape.sp_left(x), n) : Bool}
      shu.and_t(a, shu.fits(n, List.append(&2, S.St, t, ys)), shu.and_l(a, shu.fits(n, t), hx), shu.fits_app(n, t, ys, shu.and_r(a, shu.fits(n, t), hx), hy))

def shu.fits_l(+n: Nat, xs: List<&2, S.St>, +ys: List<&2, S.St>, +h: {shu.fits(n, List.append(&2, S.St, xs, ys)) == True{} : Bool}) -> {shu.fits(n, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      +a = {Nat.is_lt(Shape.sp_left(x), n) : Bool}
      shu.and_t(a, shu.fits(n, t), shu.and_l(a, shu.fits(n, List.append(&2, S.St, t, ys)), h), shu.fits_l(n, t, ys, shu.and_r(a, shu.fits(n, List.append(&2, S.St, t, ys)), h)))

def shu.one(+n: Nat, +s: S.St, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, [s]) == True{} : Bool}:
  shu.and_t(Nat.is_lt(Shape.sp_left(s), n), True{}, h, {==})

def shu.head(+n: Nat, +s: S.St, -t: List<&2, S.St>, h: {shu.fits(n, s <> t) == True{} : Bool}) -> {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}:
  shu.and_l(Nat.is_lt(Shape.sp_left(s), n), shu.fits(n, t), h)

def shu.tail(+n: Nat, +s: S.St, -t: List<&2, S.St>, h: {shu.fits(n, s <> t) == True{} : Bool}) -> {shu.fits(n, t) == True{} : Bool}:
  shu.and_r(Nat.is_lt(Shape.sp_left(s), n), shu.fits(n, t), h)

def shu.if(b: Bool, +n: Nat, +xs: List<&2, S.St>, h: {shu.fits(n, xs) == True{} : Bool}) -> {shu.fits(n, Shape.sp_if(b, xs)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

# Leaves keep their places below n
# --------------------------------

def shu.eat(u: String, +ci: Bool, s: S.St, +n: Nat, +h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_eat(u, ci, s)) == True{} : Bool}:
  match u:
    case SNil{}:
      shu.one(n, s, h)
    case SCon{+y, +v}:
      match s:
        case S.St{+pos, +left, +word, +rest, +caps}:
          match rest:
            case SNil{}:
              {==}
            case SCon{+x, +t}:
              +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
              shu.if(Shape.sp_ch_eq(ci, x, y), n, Shape.sp_eat(v, ci, s2), shu.eat(v, ci, s2, n, shu.lt_dec(left, n, h)))

def shu.zero(min: Nat, +n: Nat, +s: S.St, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_zero(min, s)) == True{} : Bool}:
  match min:
    case 0n:
      shu.one(n, s, h)
    case 1n+m:
      {==}

def shu.run_go(rest: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, +n: Nat, +h: {Nat.is_lt(left, n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_run.go(rest, c, min, max, pos, left, word, caps)) == True{} : Bool}:
  match rest:
    case SNil{}:
      shu.zero(min, n, S.St{pos, left, word, SNil{}, caps}, h)
    case SCon{+x, +t}:
      +xs = {Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
      shu.fits_app(n, Shape.sp_if(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), xs), Shape.sp_zero(min, S.St{pos, left, word, SCon{x, t}, caps}), shu.if(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), n, xs, shu.run_go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, n, shu.lt_dec(left, n, h))), shu.zero(min, n, S.St{pos, left, word, SCon{x, t}, caps}, h))

def shu.run(+c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_run(c, min, max, s)) == True{} : Bool}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      shu.run_go(rest, c, min, max, pos, left, word, caps, n, h)

def shu.same_at(m: Maybe<&2, String>, +s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_same.at(m, s)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{u}:
      shu.eat(u, False{}, s, n, h)

def shu.same(+k: Nat, s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_same(k, s)) == True{} : Bool}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shu.same_at(Shape.sp_took(k, caps), S.St{pos, left, word, rest, caps}, n, h)

def shu.bound(s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_bound(s)) == True{} : Bool}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shu.if(Bool.xor(word, Shape.sp_starts_word(rest)), n, [S.St{pos, left, word, rest, caps}], shu.one(n, S.St{pos, left, word, rest, caps}, h))

def shu.begin(s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_begin(s)) == True{} : Bool}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shu.if(Nat.is_eq(pos, 0n), n, [S.St{pos, left, word, rest, caps}], shu.one(n, S.St{pos, left, word, rest, caps}, h))

def shu.end(s: S.St, +n: Nat, h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_end(s)) == True{} : Bool}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shu.if(String.is_empty(rest), n, [S.St{pos, left, word, rest, caps}], shu.one(n, S.St{pos, left, word, rest, caps}, h))

# a capture keeps the places' counts
def shu.cap(+n: Nat, xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String) -> {shu.fits(n, Shape.sp_cap(xs, k, at, from)) == shu.fits(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case S.St{+pos, +left, word, rest, caps}:
          Equal.cong(Bool, Bool, b => Bool.and(Nat.is_lt(left, n), b), shu.fits(n, Shape.sp_cap(t, k, at, from)), shu.fits(n, t), shu.cap(n, t, k, at, from))

def shu.cap_t(+n: Nat, +xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String, h: {shu.fits(n, xs) == True{} : Bool}) -> {shu.fits(n, Shape.sp_cap(xs, k, at, from)) == True{} : Bool}:
  %Equal.sym(Bool, shu.fits(n, Shape.sp_cap(xs, k, at, from)), shu.fits(n, xs), shu.cap(n, xs, k, at, from)) : {_ == True{} : Bool}
  h

def shu.moved(+n: Nat, +l: Nat, xs: List<&2, S.St>, +h: {shu.fits(n, xs) == True{} : Bool}) -> {shu.fits(n, Shape.sp_moved(l, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      shu.fits_app(n, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]), Shape.sp_moved(l, t), shu.if(Nat.is_lt(Shape.sp_left(x), l), n, [x], shu.one(n, x, shu.head(n, x, t, h))), shu.moved(n, l, t, shu.tail(n, x, t, h)))

def shu.moved_lt.if(b: Bool, +y: S.St, +l: Nat, +g: Nat, e: {Nat.is_lt(Shape.sp_left(y), l) == b : Bool}, hl: {Nat.is_lt(l, 1n+g) == True{} : Bool}) -> {shu.fits(g, Shape.sp_if(b, [y])) == True{} : Bool}:
  match b:
    case True{}:
      shu.one(g, y, shu.lt_lt(Shape.sp_left(y), l, g, e, hl))
    case False{}:
      {==}

# the rounds that read a char from a place with l chars after it, l below
# g + 1, have fewer than g chars after them
def shu.moved_lt(+g: Nat, +l: Nat, xs: List<&2, S.St>, +hl: {Nat.is_lt(l, 1n+g) == True{} : Bool}) -> {shu.fits(g, Shape.sp_moved(l, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      shu.fits_app(g, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]), Shape.sp_moved(l, t), shu.moved_lt.if(Nat.is_lt(Shape.sp_left(x), l), x, l, g, {==}, hl), shu.moved_lt(g, l, t, hl))

def shu.ahead(+neg: Bool, xs: List<&2, S.St>, +s: S.St, +n: Nat, +h: {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}) -> {shu.fits(n, Shape.sp_ahead(neg, xs, s)) == True{} : Bool}:
  match xs:
    case Nil{}:
      shu.if(neg, n, [s], shu.one(n, s, h))
    case x <> t:
      shu.if(Bool.not(neg), n, [s], shu.one(n, s, h))

# Readings keep places below n
# ----------------------------

def shu.pf(f: Nat, ps: List<&2, S.Piece>, L: List<&2, S.St>, +base: Nat, +n: Nat, +h: {shu.fits(n, L) == True{} : Bool}) -> {shu.fits(n, Shape.sp_reads(f, ps, L, base)) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      match ps:
        case Nil{}:
          h
        case p <> +t:
          match p:
            case S.Lit{+u}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_eat(u, False{}, s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Lit{u} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.eat(u, False{}, s, n, hs)), shu.pf(1n+g, S.Lit{u} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Fold{+u}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_eat(u, True{}, s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Fold{u} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.eat(u, True{}, s, n, hs)), shu.pf(1n+g, S.Fold{u} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Run{+c, +min, +max}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_run(c, min, max, s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Run{c, min, max} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.run(c, min, max, s, n, hs)), shu.pf(1n+g, S.Run{c, min, max} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Cap{+i}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, 1n+Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g, S.Cap{i} <> t, rest, base), shu.pf(1n+g, t, r1, 1n+Nat.add(base, Shape.sp_ncaps(i)), n, shu.cap_t(n, Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), shu.pf(1n+g, i, [s], 1n+base, n, h1))), shu.pf(1n+g, S.Cap{i} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Opt{+i}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g, S.Opt{i} <> t, rest, base), shu.pf(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i)), n, shu.fits_app(n, Shape.sp_reads(1n+g, i, [s], base), [s], shu.pf(1n+g, i, [s], base, n, h1), h1)), shu.pf(1n+g, S.Opt{i} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Alt{+a, +bb}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Shape.sp_reads(1n+g, S.Alt{a, bb} <> t, rest, base), shu.pf(1n+g, t, r1, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), n, shu.fits_app(n, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), shu.pf(1n+g, a, [s], base, n, h1), shu.pf(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), n, h1))), shu.pf(1n+g, S.Alt{a, bb} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Many{+i, +min}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g, S.Many{i, min} <> t, rest, base), shu.pf(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i)), n, shu.fits_app(n, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), shu.pf(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base, n, shu.moved(n, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), shu.pf(1n+g, i, [s], base, n, h1))), shu.zero(min, n, s, hs))), shu.pf(1n+g, S.Many{i, min} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Ahead{+i, +neg}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g, S.Ahead{i, neg} <> t, rest, base), shu.pf(1n+g, t, r1, Nat.add(base, Shape.sp_ncaps(i)), n, shu.ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s, n, hs)), shu.pf(1n+g, S.Ahead{i, neg} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Same{+k}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_same(k, s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Same{k} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.same(k, s, n, hs)), shu.pf(1n+g, S.Same{k} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Bound{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_bound(s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Bound{} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.bound(s, n, hs)), shu.pf(1n+g, S.Bound{} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.Begin{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_begin(s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.Begin{} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.begin(s, n, hs)), shu.pf(1n+g, S.Begin{} <> t, rest, base, n, shu.tail(n, s, rest, h)))
            case S.End{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +hs = {shu.head(n, s, rest, h) : {Nat.is_lt(Shape.sp_left(s), n) == True{} : Bool}}
                  +h1 = {shu.one(n, s, hs) : {shu.fits(n, [s]) == True{} : Bool}}
                  +r1 = {Shape.sp_end(s) : List<&2, S.St>}
                  shu.fits_app(n, Shape.sp_reads(1n+g, t, r1, base), Shape.sp_reads(1n+g, S.End{} <> t, rest, base), shu.pf(1n+g, t, r1, base, n, shu.end(s, n, hs)), shu.pf(1n+g, S.End{} <> t, rest, base, n, shu.tail(n, s, rest, h)))

def shu.app2(-X1: List<&2, S.St>, -X2: List<&2, S.St>, -Y1: List<&2, S.St>, -Y2: List<&2, S.St>, h1: {X1 == Y1 : List<&2, S.St>}, h2: {X2 == Y2 : List<&2, S.St>}) -> {List.append(&2, S.St, X1, X2) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, X1, Y1, h1) : {List.append(&2, S.St, _, X2) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}
  %Equal.sym(List<&2, S.St>, X2, Y2, h2) : {List.append(&2, S.St, Y1, _) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}
  {==}

# no place of a list fits below 0
def shu.fits0(-G: Type, +x: S.St, -t: List<&2, S.St>, h: {shu.fits(0n, x <> t) == True{} : Bool}) -> G:
  +a = {Nat.is_lt(Shape.sp_left(x), 0n) : Bool}
  shu.absurd(G, Equal.trans(Bool, False{}, a, True{}, Equal.sym(Bool, a, False{}, shu.lt_zero(Shape.sp_left(x))), shu.and_l(a, shu.fits(0n, t), h)))

# any fuel past the chars after every place of L reads the same readings
def shu.fi(f1: Nat, f2: Nat, ps: List<&2, S.Piece>, L: List<&2, S.St>, +base: Nat, +h1: {shu.fits(f1, L) == True{} : Bool}, +h2: {shu.fits(f2, L) == True{} : Bool}) -> {Shape.sp_reads(f1, ps, L, base) == Shape.sp_reads(f2, ps, L, base) : List<&2, S.St>}:
  match f1:
    case 0n:
      match L:
        case Nil{}:
          Equal.sym(List<&2, S.St>, Shape.sp_reads(f2, ps, Nil{}, base), Nil{}, LH.shh.reads_nil(f2, ps, base))
        case +x <> t:
          shu.fits0({Shape.sp_reads(0n, ps, x <> t, base) == Shape.sp_reads(f2, ps, x <> t, base) : List<&2, S.St>}, x, t, h1)
    case 1n++g1:
      match f2:
        case 0n:
          match L:
            case Nil{}:
              LH.shh.reads_nil(1n+g1, ps, base)
            case +x <> t:
              shu.fits0({Shape.sp_reads(1n+g1, ps, x <> t, base) == Shape.sp_reads(0n, ps, x <> t, base) : List<&2, S.St>}, x, t, h2)
        case 1n++g2:
          match ps:
            case Nil{}:
              {==}
            case p <> +t:
              match p:
                case S.Lit{+u}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_eat(u, False{}, s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Lit{u} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Lit{u} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.eat(u, False{}, s, 1n+g1, hs1), shu.eat(u, False{}, s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Lit{u} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Fold{+u}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_eat(u, True{}, s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Fold{u} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Fold{u} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.eat(u, True{}, s, 1n+g1, hs1), shu.eat(u, True{}, s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Fold{u} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Run{+c, +min, +max}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_run(c, min, max, s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Run{c, min, max} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Run{c, min, max} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.run(c, min, max, s, 1n+g1, hs1), shu.run(c, min, max, s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Run{c, min, max} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Cap{+i}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_cap(Shape.sp_reads(1n+g2, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
                      +r1 = {Shape.sp_cap(Shape.sp_reads(1n+g1, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r1, 1n+Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, S.Cap{i} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, 1n+Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, S.Cap{i} <> t, rest, base), Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g1, t, r1, 1n+Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, t, r2, 1n+Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, t, r2, 1n+Nat.add(base, Shape.sp_ncaps(i))), Equal.cong(List<&2, S.St>, List<&2, S.St>, r => Shape.sp_reads(1n+g1, t, r, 1n+Nat.add(base, Shape.sp_ncaps(i))), r1, r2, Equal.cong(List<&2, S.St>, List<&2, S.St>, X => Shape.sp_cap(X, base, Shape.sp_pos(s), Shape.sp_text(s)), Shape.sp_reads(1n+g1, i, [s], 1n+base), Shape.sp_reads(1n+g2, i, [s], 1n+base), shu.fi(1n+g1, 1n+g2, i, [s], 1n+base, h11, h12))), shu.fi(1n+g1, 1n+g2, t, r2, 1n+Nat.add(base, Shape.sp_ncaps(i)), shu.cap_t(1n+g1, Shape.sp_reads(1n+g2, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), shu.pf(1n+g2, i, [s], 1n+base, 1n+g1, h11)), shu.cap_t(1n+g2, Shape.sp_reads(1n+g2, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), shu.pf(1n+g2, i, [s], 1n+base, 1n+g2, h12)))), shu.fi(1n+g1, 1n+g2, S.Cap{i} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Opt{+i}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {List.append(&2, S.St, Shape.sp_reads(1n+g2, i, [s], base), [s]) : List<&2, S.St>}
                      +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g1, i, [s], base), [s]) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, S.Opt{i} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, S.Opt{i} <> t, rest, base), Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Equal.cong(List<&2, S.St>, List<&2, S.St>, r => Shape.sp_reads(1n+g1, t, r, Nat.add(base, Shape.sp_ncaps(i))), r1, r2, Equal.cong(List<&2, S.St>, List<&2, S.St>, X => List.append(&2, S.St, X, [s]), Shape.sp_reads(1n+g1, i, [s], base), Shape.sp_reads(1n+g2, i, [s], base), shu.fi(1n+g1, 1n+g2, i, [s], base, h11, h12))), shu.fi(1n+g1, 1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i)), shu.fits_app(1n+g1, Shape.sp_reads(1n+g2, i, [s], base), [s], shu.pf(1n+g2, i, [s], base, 1n+g1, h11), h11), shu.fits_app(1n+g2, Shape.sp_reads(1n+g2, i, [s], base), [s], shu.pf(1n+g2, i, [s], base, 1n+g2, h12), h12))), shu.fi(1n+g1, 1n+g2, S.Opt{i} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Alt{+a, +bb}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {List.append(&2, S.St, Shape.sp_reads(1n+g2, a, [s], base), Shape.sp_reads(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) : List<&2, S.St>}
                      +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g1, a, [s], base), Shape.sp_reads(1n+g1, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r1, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Shape.sp_reads(1n+g1, S.Alt{a, bb} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Shape.sp_reads(1n+g2, S.Alt{a, bb} <> t, rest, base), Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g1, t, r1, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Shape.sp_reads(1n+g1, t, r2, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Shape.sp_reads(1n+g2, t, r2, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Equal.cong(List<&2, S.St>, List<&2, S.St>, r => Shape.sp_reads(1n+g1, t, r, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), r1, r2, shu.app2(Shape.sp_reads(1n+g1, a, [s], base), Shape.sp_reads(1n+g1, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), Shape.sp_reads(1n+g2, a, [s], base), Shape.sp_reads(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), shu.fi(1n+g1, 1n+g2, a, [s], base, h11, h12), shu.fi(1n+g1, 1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), h11, h12))), shu.fi(1n+g1, 1n+g2, t, r2, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), shu.fits_app(1n+g1, Shape.sp_reads(1n+g2, a, [s], base), Shape.sp_reads(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), shu.pf(1n+g2, a, [s], base, 1n+g1, h11), shu.pf(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), 1n+g1, h11)), shu.fits_app(1n+g2, Shape.sp_reads(1n+g2, a, [s], base), Shape.sp_reads(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), shu.pf(1n+g2, a, [s], base, 1n+g2, h12), shu.pf(1n+g2, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), 1n+g2, h12)))), shu.fi(1n+g1, 1n+g2, S.Alt{a, bb} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Many{+i, +min}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {List.append(&2, S.St, Shape.sp_reads(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
                      +r1 = {List.append(&2, S.St, Shape.sp_reads(g1, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g1, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, S.Many{i, min} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, S.Many{i, min} <> t, rest, base), Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Equal.cong(List<&2, S.St>, List<&2, S.St>, r => Shape.sp_reads(1n+g1, t, r, Nat.add(base, Shape.sp_ncaps(i))), r1, r2, Equal.trans(List<&2, S.St>, List.append(&2, S.St, Shape.sp_reads(g1, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g1, i, [s], base)), base), Shape.sp_zero(min, s)), List.append(&2, S.St, Shape.sp_reads(g1, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_zero(min, s)), List.append(&2, S.St, Shape.sp_reads(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_zero(min, s)), Equal.cong(List<&2, S.St>, List<&2, S.St>, X => List.append(&2, S.St, Shape.sp_reads(g1, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), X), base), Shape.sp_zero(min, s)), Shape.sp_reads(1n+g1, i, [s], base), Shape.sp_reads(1n+g2, i, [s], base), shu.fi(1n+g1, 1n+g2, i, [s], base, h11, h12)), Equal.cong(List<&2, S.St>, List<&2, S.St>, Y => List.append(&2, S.St, Y, Shape.sp_zero(min, s)), Shape.sp_reads(g1, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_reads(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), shu.fi(g1, g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base, shu.moved_lt(g1, Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base), hs1), shu.moved_lt(g2, Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base), hs2))))), shu.fi(1n+g1, 1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i)), shu.fits_app(1n+g1, Shape.sp_reads(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_zero(min, s), shu.pf(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base, 1n+g1, shu.moved(1n+g1, Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base), shu.pf(1n+g2, i, [s], base, 1n+g1, h11))), shu.zero(min, 1n+g1, s, hs1)), shu.fits_app(1n+g2, Shape.sp_reads(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base), Shape.sp_zero(min, s), shu.pf(g2, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base)), base, 1n+g2, shu.moved(1n+g2, Shape.sp_left(s), Shape.sp_reads(1n+g2, i, [s], base), shu.pf(1n+g2, i, [s], base, 1n+g2, h12))), shu.zero(min, 1n+g2, s, hs2)))), shu.fi(1n+g1, 1n+g2, S.Many{i, min} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Ahead{+i, +neg}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_ahead(neg, Shape.sp_reads(1n+g2, i, [s], base), s) : List<&2, S.St>}
                      +r1 = {Shape.sp_ahead(neg, Shape.sp_reads(1n+g1, i, [s], base), s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, S.Ahead{i, neg} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, S.Ahead{i, neg} <> t, rest, base), Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g1, t, r1, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g1, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Shape.sp_reads(1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i))), Equal.cong(List<&2, S.St>, List<&2, S.St>, r => Shape.sp_reads(1n+g1, t, r, Nat.add(base, Shape.sp_ncaps(i))), r1, r2, Equal.cong(List<&2, S.St>, List<&2, S.St>, X => Shape.sp_ahead(neg, X, s), Shape.sp_reads(1n+g1, i, [s], base), Shape.sp_reads(1n+g2, i, [s], base), shu.fi(1n+g1, 1n+g2, i, [s], base, h11, h12))), shu.fi(1n+g1, 1n+g2, t, r2, Nat.add(base, Shape.sp_ncaps(i)), shu.ahead(neg, Shape.sp_reads(1n+g2, i, [s], base), s, 1n+g1, hs1), shu.ahead(neg, Shape.sp_reads(1n+g2, i, [s], base), s, 1n+g2, hs2))), shu.fi(1n+g1, 1n+g2, S.Ahead{i, neg} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Same{+k}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_same(k, s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Same{k} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Same{k} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.same(k, s, 1n+g1, hs1), shu.same(k, s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Same{k} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Bound{}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_bound(s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Bound{} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Bound{} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.bound(s, 1n+g1, hs1), shu.bound(s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Bound{} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.Begin{}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_begin(s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.Begin{} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.Begin{} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.begin(s, 1n+g1, hs1), shu.begin(s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.Begin{} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))
                case S.End{}:
                  match L:
                    case Nil{}:
                      {==}
                    case +s <> +rest:
                      +hs1 = {shu.head(1n+g1, s, rest, h1) : {Nat.is_lt(Shape.sp_left(s), 1n+g1) == True{} : Bool}}
                      +hs2 = {shu.head(1n+g2, s, rest, h2) : {Nat.is_lt(Shape.sp_left(s), 1n+g2) == True{} : Bool}}
                      +h11 = {shu.one(1n+g1, s, hs1) : {shu.fits(1n+g1, [s]) == True{} : Bool}}
                      +h12 = {shu.one(1n+g2, s, hs2) : {shu.fits(1n+g2, [s]) == True{} : Bool}}
                      +r2 = {Shape.sp_end(s) : List<&2, S.St>}
                      shu.app2(Shape.sp_reads(1n+g1, t, r2, base), Shape.sp_reads(1n+g1, S.End{} <> t, rest, base), Shape.sp_reads(1n+g2, t, r2, base), Shape.sp_reads(1n+g2, S.End{} <> t, rest, base), shu.fi(1n+g1, 1n+g2, t, r2, base, shu.end(s, 1n+g1, hs1), shu.end(s, 1n+g2, hs2)), shu.fi(1n+g1, 1n+g2, S.End{} <> t, rest, base, shu.tail(1n+g1, s, rest, h1), shu.tail(1n+g2, s, rest, h2)))

