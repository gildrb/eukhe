# eukhe: the eager reader S.go reads exactly the spec's readings
# (shall.all), by induction along S.go: each piece's own readings equal
# the spec's (proof/shape/base/leaf.bend; the inner pieces by induction),
# then the rest of the pieces and the rest of the places.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./leaf.bend as LL

# two halves equal, their concatenations equal
def shall.app(-X1: List<&2, S.St>, -X2: List<&2, S.St>, -Y1: List<&2, S.St>, -Y2: List<&2, S.St>, h1: {X1 == Y1 : List<&2, S.St>}, h2: {X2 == Y2 : List<&2, S.St>}) -> {List.append(&2, S.St, X1, X2) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, X1, Y1, h1) : {List.append(&2, S.St, _, X2) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}
  %Equal.sym(List<&2, S.St>, X2, Y2, h2) : {List.append(&2, S.St, Y1, _) == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}
  {==}

# the rest of the pieces read from equal places with equal capture
# numbers
def shall.via(+g: Nat, +t: List<&2, S.Piece>, -Rc: List<&2, S.St>, -Rs: List<&2, S.St>, -bc: Nat, -bs: Nat, hR: {Rc == Rs : List<&2, S.St>}, hb: {bc == bs : Nat}, ih: {S.go(1n+g, t, Rs, bs) == Shape.sp_reads(1n+g, t, Rs, bs) : List<&2, S.St>}) -> {S.go(1n+g, t, Rc, bc) == Shape.sp_reads(1n+g, t, Rs, bs) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, Rc, Rs, hR) : {S.go(1n+g, t, _, bc) == Shape.sp_reads(1n+g, t, Rs, bs) : List<&2, S.St>}
  %Equal.sym(Nat, bc, bs, hb) : {S.go(1n+g, t, Rs, _) == Shape.sp_reads(1n+g, t, Rs, bs) : List<&2, S.St>}
  ih

def shall.ncaps1(+base: Nat, +i: List<&2, S.Piece>) -> {1n+Nat.add(base, S.ncaps(i)) == 1n+Nat.add(base, Shape.sp_ncaps(i)) : Nat}:
  Equal.cong(Nat, Nat, n => 1n+Nat.add(base, n), S.ncaps(i), Shape.sp_ncaps(i), LL.shl.ncaps(i))

def shall.ncaps0(+base: Nat, +i: List<&2, S.Piece>) -> {Nat.add(base, S.ncaps(i)) == Nat.add(base, Shape.sp_ncaps(i)) : Nat}:
  Equal.cong(Nat, Nat, n => Nat.add(base, n), S.ncaps(i), Shape.sp_ncaps(i), LL.shl.ncaps(i))

def shall.ncaps2(+base: Nat, +a: List<&2, S.Piece>, +b: List<&2, S.Piece>) -> {Nat.add(Nat.add(base, S.ncaps(a)), S.ncaps(b)) == Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(b)) : Nat}:
  %Equal.sym(Nat, S.ncaps(a), Shape.sp_ncaps(a), LL.shl.ncaps(a)) : {Nat.add(Nat.add(base, _), S.ncaps(b)) == Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(b)) : Nat}
  %Equal.sym(Nat, S.ncaps(b), Shape.sp_ncaps(b), LL.shl.ncaps(b)) : {Nat.add(Nat.add(base, Shape.sp_ncaps(a)), _) == Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(b)) : Nat}
  {==}

# Cap: the inner readings, captured
def shall.cap(+g: Nat, +i: List<&2, S.Piece>, +s: S.St, +base: Nat, ih: {S.go(1n+g, i, [s], 1n+base) == Shape.sp_reads(1n+g, i, [s], 1n+base) : List<&2, S.St>}) -> {S.close(S.go(1n+g, i, [s], 1n+base), base, S.place(s), S.after(s)) == Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, S.go(1n+g, i, [s], 1n+base), Shape.sp_reads(1n+g, i, [s], 1n+base), ih) : {S.close(_, base, S.place(s), S.after(s)) == Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
  %Equal.sym(Nat, S.place(s), Shape.sp_pos(s), LL.shl.place(s)) : {S.close(Shape.sp_reads(1n+g, i, [s], 1n+base), base, _, S.after(s)) == Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
  %Equal.sym(String, S.after(s), Shape.sp_text(s), LL.shl.after(s)) : {S.close(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), _) == Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
  LL.shl.close(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s))

# Many: the rounds that read a char, then more rounds, then none
def shall.many(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +s: S.St, +base: Nat, hi: {S.go(1n+g, i, [s], base) == Shape.sp_reads(1n+g, i, [s], base) : List<&2, S.St>}, hm: {S.go(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base) == Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base) : List<&2, S.St>}) -> {List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], S.grew(S.remain(s), S.go(1n+g, i, [s], base)), base), S.m2l(S.zero(min, s))) == List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, S.go(1n+g, i, [s], base), Shape.sp_reads(1n+g, i, [s], base), hi) : {List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], S.grew(S.remain(s), _), base), S.m2l(S.zero(min, s))) == List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
  %Equal.sym(Nat, S.remain(s), Shape.sp_left(s), LL.shl.remain(s)) : {List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], S.grew(_, Shape.sp_reads(1n+g, i, [s], base)), base), S.m2l(S.zero(min, s))) == List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
  %Equal.sym(List<&2, S.St>, S.grew(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), LL.shl.grew(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base))) : {List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], _, base), S.m2l(S.zero(min, s))) == List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
  %Equal.sym(Nat, S.pred(min), Shape.sp_dec(min), LL.shl.pred(min)) : {List.append(&2, S.St, S.go(g, [S.Many{i, _}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), S.m2l(S.zero(min, s))) == List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
  shall.app(S.go(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), S.m2l(S.zero(min, s)), Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), hm, LL.shl.zero(min, s))

# Ahead: the place kept by whether the inner pieces have a reading
def shall.ahead(+g: Nat, +i: List<&2, S.Piece>, +neg: Bool, +s: S.St, +base: Nat, hi: {S.go(1n+g, i, [s], base) == Shape.sp_reads(1n+g, i, [s], base) : List<&2, S.St>}) -> {S.ahead.if(neg, S.go(1n+g, i, [s], base), s) == Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s) : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, S.go(1n+g, i, [s], base), Shape.sp_reads(1n+g, i, [s], base), hi) : {S.ahead.if(neg, _, s) == Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s) : List<&2, S.St>}
  LL.shl.ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s)

def shall.all(f: Nat, ps: List<&2, S.Piece>, L: List<&2, S.St>, +base: Nat) -> {S.go(f, ps, L, base) == Shape.sp_reads(f, ps, L, base) : List<&2, S.St>}:
  match f:
    case 0n:
      {==}
    case 1n++g:
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
                  +rs = {Shape.sp_eat(u, False{}, s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Lit{u}, s), base), S.go(1n+g, S.Lit{u} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Lit{u} <> t, rest, base), shall.via(g, t, S.leaf(S.Lit{u}, s), rs, base, base, LL.shl.lit(u, False{}, s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Lit{u} <> t, rest, base))
            case S.Fold{+u}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_eat(u, True{}, s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Fold{u}, s), base), S.go(1n+g, S.Fold{u} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Fold{u} <> t, rest, base), shall.via(g, t, S.leaf(S.Fold{u}, s), rs, base, base, LL.shl.lit(u, True{}, s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Fold{u} <> t, rest, base))
            case S.Run{+c, +need, +room}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_run(c, need, room, s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Run{c, need, room}, s), base), S.go(1n+g, S.Run{c, need, room} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Run{c, need, room} <> t, rest, base), shall.via(g, t, S.leaf(S.Run{c, need, room}, s), rs, base, base, LL.shl.run(c, need, room, s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Run{c, need, room} <> t, rest, base))
            case S.Cap{+i}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rc = {S.close(S.go(1n+g, i, [s], 1n+base), base, S.place(s), S.after(s)) : List<&2, S.St>}
                  +rs = {Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
                  +bc = {1n+Nat.add(base, S.ncaps(i)) : Nat}
                  +bs = {1n+Nat.add(base, Shape.sp_ncaps(i)) : Nat}
                  shall.app(S.go(1n+g, t, rc, bc), S.go(1n+g, S.Cap{i} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, bs), Shape.sp_reads(1n+g, S.Cap{i} <> t, rest, base), shall.via(g, t, rc, rs, bc, bs, shall.cap(g, i, s, base, shall.all(1n+g, i, [s], 1n+base)), shall.ncaps1(base, i), shall.all(1n+g, t, rs, bs)), shall.all(1n+g, S.Cap{i} <> t, rest, base))
            case S.Opt{+i}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rc = {List.append(&2, S.St, S.go(1n+g, i, [s], base), [s]) : List<&2, S.St>}
                  +rs = {List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]) : List<&2, S.St>}
                  +bc = {Nat.add(base, S.ncaps(i)) : Nat}
                  +bs = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
                  shall.app(S.go(1n+g, t, rc, bc), S.go(1n+g, S.Opt{i} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, bs), Shape.sp_reads(1n+g, S.Opt{i} <> t, rest, base), shall.via(g, t, rc, rs, bc, bs, shall.app(S.go(1n+g, i, [s], base), [s], Shape.sp_reads(1n+g, i, [s], base), [s], shall.all(1n+g, i, [s], base), {==}), shall.ncaps0(base, i), shall.all(1n+g, t, rs, bs)), shall.all(1n+g, S.Opt{i} <> t, rest, base))
            case S.Alt{+a, +b}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rc = {List.append(&2, S.St, S.go(1n+g, a, [s], base), S.go(1n+g, b, [s], Nat.add(base, S.ncaps(a)))) : List<&2, S.St>}
                  +rs = {List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a)))) : List<&2, S.St>}
                  +bc = {Nat.add(Nat.add(base, S.ncaps(a)), S.ncaps(b)) : Nat}
                  +bs = {Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(b)) : Nat}
                  +hb = {Equal.trans(List<&2, S.St>, S.go(1n+g, b, [s], Nat.add(base, S.ncaps(a))), S.go(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a))), Shape.sp_reads(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a))), Equal.cong(Nat, List<&2, S.St>, n => S.go(1n+g, b, [s], n), Nat.add(base, S.ncaps(a)), Nat.add(base, Shape.sp_ncaps(a)), shall.ncaps0(base, a)), shall.all(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a)))) : {S.go(1n+g, b, [s], Nat.add(base, S.ncaps(a))) == Shape.sp_reads(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a))) : List<&2, S.St>}}
                  shall.app(S.go(1n+g, t, rc, bc), S.go(1n+g, S.Alt{a, b} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, bs), Shape.sp_reads(1n+g, S.Alt{a, b} <> t, rest, base), shall.via(g, t, rc, rs, bc, bs, shall.app(S.go(1n+g, a, [s], base), S.go(1n+g, b, [s], Nat.add(base, S.ncaps(a))), Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, b, [s], Nat.add(base, Shape.sp_ncaps(a))), shall.all(1n+g, a, [s], base), hb), shall.ncaps2(base, a, b), shall.all(1n+g, t, rs, bs)), shall.all(1n+g, S.Alt{a, b} <> t, rest, base))
            case S.Many{+i, +min}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rc = {List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], S.grew(S.remain(s), S.go(1n+g, i, [s], base)), base), S.m2l(S.zero(min, s))) : List<&2, S.St>}
                  +mv = {Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)) : List<&2, S.St>}
                  +rs = {List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], mv, base), Shape.sp_zero(min, s)) : List<&2, S.St>}
                  +bc = {Nat.add(base, S.ncaps(i)) : Nat}
                  +bs = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
                  shall.app(S.go(1n+g, t, rc, bc), S.go(1n+g, S.Many{i, min} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, bs), Shape.sp_reads(1n+g, S.Many{i, min} <> t, rest, base), shall.via(g, t, rc, rs, bc, bs, shall.many(g, i, min, s, base, shall.all(1n+g, i, [s], base), shall.all(g, [S.Many{i, Shape.sp_dec(min)}], mv, base)), shall.ncaps0(base, i), shall.all(1n+g, t, rs, bs)), shall.all(1n+g, S.Many{i, min} <> t, rest, base))
            case S.Ahead{+i, +neg}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rc = {S.ahead.if(neg, S.go(1n+g, i, [s], base), s) : List<&2, S.St>}
                  +rs = {Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s) : List<&2, S.St>}
                  +bc = {Nat.add(base, S.ncaps(i)) : Nat}
                  +bs = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
                  shall.app(S.go(1n+g, t, rc, bc), S.go(1n+g, S.Ahead{i, neg} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, bs), Shape.sp_reads(1n+g, S.Ahead{i, neg} <> t, rest, base), shall.via(g, t, rc, rs, bc, bs, shall.ahead(g, i, neg, s, base, shall.all(1n+g, i, [s], base)), shall.ncaps0(base, i), shall.all(1n+g, t, rs, bs)), shall.all(1n+g, S.Ahead{i, neg} <> t, rest, base))
            case S.Same{+k}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_same(k, s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Same{k}, s), base), S.go(1n+g, S.Same{k} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Same{k} <> t, rest, base), shall.via(g, t, S.leaf(S.Same{k}, s), rs, base, base, LL.shl.same_k(k, s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Same{k} <> t, rest, base))
            case S.Bound{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_bound(s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Bound{}, s), base), S.go(1n+g, S.Bound{} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Bound{} <> t, rest, base), shall.via(g, t, S.leaf(S.Bound{}, s), rs, base, base, LL.shl.bound(s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Bound{} <> t, rest, base))
            case S.Begin{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_begin(s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.Begin{}, s), base), S.go(1n+g, S.Begin{} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.Begin{} <> t, rest, base), shall.via(g, t, S.leaf(S.Begin{}, s), rs, base, base, LL.shl.begin(s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.Begin{} <> t, rest, base))
            case S.End{}:
              match L:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +rs = {Shape.sp_end(s) : List<&2, S.St>}
                  shall.app(S.go(1n+g, t, S.leaf(S.End{}, s), base), S.go(1n+g, S.End{} <> t, rest, base), Shape.sp_reads(1n+g, t, rs, base), Shape.sp_reads(1n+g, S.End{} <> t, rest, base), shall.via(g, t, S.leaf(S.End{}, s), rs, base, base, LL.shl.end(s), {==}, shall.all(1n+g, t, rs, base)), shall.all(1n+g, S.End{} <> t, rest, base))
