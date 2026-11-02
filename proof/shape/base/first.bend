# eukhe: the matcher's first mode answers the first reading of its all
# mode whose end condition holds (shf.first), by induction along S.go.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA

def shf.step(+e: Bool, +xs: List<&2, S.St>, +ys: List<&2, S.St>, -xf: List<&2, S.St>, -yf: List<&2, S.St>, ix: {xf == LA.shb.take1(Shape.sp_keep(e, xs)) : List<&2, S.St>}, iy: {yf == LA.shb.take1(Shape.sp_keep(e, ys)) : List<&2, S.St>}) -> {S.join(S.First{e}, xf, k => yf) == LA.shb.take1(Shape.sp_keep(e, List.append(&2, S.St, xs, ys))) : List<&2, S.St>}:
  LA.shb.first_step(e, xs, ys, xf, yf, Equal.sym(List<&2, S.St>, xf, LA.shb.take1(Shape.sp_keep(e, xs)), ix), Equal.sym(List<&2, S.St>, yf, LA.shb.take1(Shape.sp_keep(e, ys)), iy))

# a place every piece has read: the first mode's place is the first of
# the all mode's, kept by the end condition
def shf.done(+e: Bool, s: S.St) -> {LA.shb.take1(Shape.sp_keep(e, [s])) == S.done(S.First{e}, s) : List<&2, S.St>}:
  match e:
    case False{}:
      {==}
    case True{}:
      match s:
        case S.St{pos, left, word, rest, caps}:
          match rest:
            case SNil{}:
              {==}
            case SCon{x, t}:
              {==}

def shf.first(f: Nat, ps: List<&2, S.Piece>, L: List<&2, S.St>, +base: Nat, +e: Bool) -> {S.go(f, ps, L, base, S.First{e}) == LA.shb.take1(Shape.sp_keep(e, S.go(f, ps, L, base, S.All{}))) : List<&2, S.St>}:
  match f:
    case 0n:
      LA.shb.take1_nil(e)
    case 1n++g:
      match ps:
        case Nil{}:
          match L:
            case Nil{}:
              LA.shb.take1_nil(e)
            case +s <> +rest:
              LA.shb.first_step(e, [s], S.go(1n+g, Nil{}, rest, base, S.All{}), S.done(S.First{e}, s), S.go(1n+g, Nil{}, rest, base, S.First{e}), shf.done(e, s), Equal.sym(List<&2, S.St>, S.go(1n+g, Nil{}, rest, base, S.First{e}), LA.shb.take1(Shape.sp_keep(e, S.go(1n+g, Nil{}, rest, base, S.All{}))), shf.first(1n+g, Nil{}, rest, base, e)))
        case p <> +t:
          match p:
            case S.Lit{+u}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Lit{u}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Lit{u} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Lit{u} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Lit{u} <> t, rest, base, e))
            case S.Fold{+u}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Fold{u}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Fold{u} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Fold{u} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Fold{u} <> t, rest, base, e))
            case S.Run{+c, +need, +room}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Run{c, need, room}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Run{c, need, room} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Run{c, need, room} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Run{c, need, room} <> t, rest, base, e))
            case S.Cap{+i}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.close(S.go(1n+g, i, [s], 1n+base, S.All{}), base, S.place(s), S.after(s))
                  +b = {1n+Nat.add(base, S.ncaps(i)) : Nat}
                  shf.step(e, S.go(1n+g, t, r, b, S.All{}), S.go(1n+g, S.Cap{i} <> t, rest, base, S.All{}), S.go(1n+g, t, r, b, S.First{e}), S.go(1n+g, S.Cap{i} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, b, e), shf.first(1n+g, S.Cap{i} <> t, rest, base, e))
            case S.Opt{+i}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = List.append(&2, S.St, S.go(1n+g, i, [s], base, S.All{}), [s])
                  +b = {Nat.add(base, S.ncaps(i)) : Nat}
                  shf.step(e, S.go(1n+g, t, r, b, S.All{}), S.go(1n+g, S.Opt{i} <> t, rest, base, S.All{}), S.go(1n+g, t, r, b, S.First{e}), S.go(1n+g, S.Opt{i} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, b, e), shf.first(1n+g, S.Opt{i} <> t, rest, base, e))
            case S.Alt{+a, +bb}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = List.append(&2, S.St, S.go(1n+g, a, [s], base, S.All{}), S.go(1n+g, bb, [s], Nat.add(base, S.ncaps(a)), S.All{}))
                  +b = {Nat.add(Nat.add(base, S.ncaps(a)), S.ncaps(bb)) : Nat}
                  shf.step(e, S.go(1n+g, t, r, b, S.All{}), S.go(1n+g, S.Alt{a, bb} <> t, rest, base, S.All{}), S.go(1n+g, t, r, b, S.First{e}), S.go(1n+g, S.Alt{a, bb} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, b, e), shf.first(1n+g, S.Alt{a, bb} <> t, rest, base, e))
            case S.Many{+i, +min}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = List.append(&2, S.St, S.go(g, [S.Many{i, S.pred(min)}], S.grew(S.remain(s), S.go(1n+g, i, [s], base, S.All{})), base, S.All{}), S.many.zero(min, s))
                  +b = {Nat.add(base, S.ncaps(i)) : Nat}
                  shf.step(e, S.go(1n+g, t, r, b, S.All{}), S.go(1n+g, S.Many{i, min} <> t, rest, base, S.All{}), S.go(1n+g, t, r, b, S.First{e}), S.go(1n+g, S.Many{i, min} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, b, e), shf.first(1n+g, S.Many{i, min} <> t, rest, base, e))
            case S.Ahead{+i, +neg}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.ahead.if(neg, S.go(1n+g, i, [s], base, S.First{False{}}), s)
                  +b = {Nat.add(base, S.ncaps(i)) : Nat}
                  shf.step(e, S.go(1n+g, t, r, b, S.All{}), S.go(1n+g, S.Ahead{i, neg} <> t, rest, base, S.All{}), S.go(1n+g, t, r, b, S.First{e}), S.go(1n+g, S.Ahead{i, neg} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, b, e), shf.first(1n+g, S.Ahead{i, neg} <> t, rest, base, e))
            case S.Same{+k}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Same{k}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Same{k} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Same{k} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Same{k} <> t, rest, base, e))
            case S.Bound{}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Bound{}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Bound{} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Bound{} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Bound{} <> t, rest, base, e))
            case S.Begin{}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.Begin{}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.Begin{} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.Begin{} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.Begin{} <> t, rest, base, e))
            case S.End{}:
              match L:
                case Nil{}:
                  LA.shb.take1_nil(e)
                case +s <> +rest:
                  +r = S.leaf(S.End{}, s)
                  shf.step(e, S.go(1n+g, t, r, base, S.All{}), S.go(1n+g, S.End{} <> t, rest, base, S.All{}), S.go(1n+g, t, r, base, S.First{e}), S.go(1n+g, S.End{} <> t, rest, base, S.First{e}), shf.first(1n+g, t, r, base, e), shf.first(1n+g, S.End{} <> t, rest, base, e))
