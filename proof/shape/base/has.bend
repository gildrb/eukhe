# eukhe: membership of a place in a list of places (Shape.sp_has), and
# the readings of a list of places as the readings of each place in turn.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA

# Membership
# ----------

def shh.app_l(-x: S.St, xs: List<&2, S.St>, -ys: List<&2, S.St>, h: Shape.sp_has(x, xs)) -> Shape.sp_has(x, List.append(&2, S.St, xs, ys)):
  match xs:
    case Nil{}:
      match h:
    case c <> t:
      match h:
        case Inl{e}:
          Inl{e}
        case Inr{k}:
          Inr{shh.app_l(x, t, ys, k)}

def shh.app_r(-x: S.St, xs: List<&2, S.St>, -ys: List<&2, S.St>, h: Shape.sp_has(x, ys)) -> Shape.sp_has(x, List.append(&2, S.St, xs, ys)):
  match xs:
    case Nil{}:
      h
    case c <> t:
      Inr{shh.app_r(x, t, ys, h)}

def shh.lift(-x: S.St, -c: S.St, -t: List<&2, S.St>, -ys: List<&2, S.St>, r: Shape.sp_has(x, t) | Shape.sp_has(x, ys)) -> Shape.sp_has(x, c <> t) | Shape.sp_has(x, ys):
  match r:
    case Inl{a}:
      Inl{Inr{a}}
    case Inr{b}:
      Inr{b}

def shh.app_split(-x: S.St, xs: List<&2, S.St>, -ys: List<&2, S.St>, h: Shape.sp_has(x, List.append(&2, S.St, xs, ys))) -> Shape.sp_has(x, xs) | Shape.sp_has(x, ys):
  match xs:
    case Nil{}:
      Inr{h}
    case c <> t:
      match h:
        case Inl{e}:
          Inl{Inl{e}}
        case Inr{k}:
          shh.lift(x, c, t, ys, shh.app_split(x, t, ys, k))

# the one place of a list of one
def shh.single(-x: S.St, -s: S.St, h: Shape.sp_has(x, [s])) -> {s == x : S.St}:
  match h:
    case Inl{e}:
      e
    case Inr{k}:
      match k:

def shh.one(+s: S.St) -> Shape.sp_has(s, [s]):
  Inl{{==}}

# Readings of a list of places
# ----------------------------

def shh.reads_nil(f: Nat, ps: List<&2, S.Piece>, +base: Nat) -> {Shape.sp_reads(f, ps, Nil{}, base) == Nil{} : List<&2, S.St>}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      match ps:
        case Nil{}:
          {==}
        case p <> t:
          match p:
            case S.Lit{u}:
              {==}
            case S.Fold{u}:
              {==}
            case S.Run{c, min, max}:
              {==}
            case S.Cap{i}:
              {==}
            case S.Opt{i}:
              {==}
            case S.Alt{a, bb}:
              {==}
            case S.Many{i, min}:
              {==}
            case S.Ahead{i, neg}:
              {==}
            case S.Same{k}:
              {==}
            case S.Bound{}:
              {==}
            case S.Begin{}:
              {==}
            case S.End{}:
              {==}

def shh.app_step(-A: List<&2, S.St>, -X: List<&2, S.St>, +Y1: List<&2, S.St>, +Y2: List<&2, S.St>, ih: {X == List.append(&2, S.St, Y1, Y2) : List<&2, S.St>}, +A2: List<&2, S.St>, ea: {A2 == A : List<&2, S.St>}) -> {List.append(&2, S.St, A, X) == List.append(&2, S.St, List.append(&2, S.St, A, Y1), Y2) : List<&2, S.St>}:
  %ea : {List.append(&2, S.St, _, X) == List.append(&2, S.St, List.append(&2, S.St, _, Y1), Y2) : List<&2, S.St>}
  %Equal.sym(List<&2, S.St>, X, List.append(&2, S.St, Y1, Y2), ih) : {List.append(&2, S.St, A2, _) == List.append(&2, S.St, List.append(&2, S.St, A2, Y1), Y2) : List<&2, S.St>}
  Equal.sym(List<&2, S.St>, List.append(&2, S.St, List.append(&2, S.St, A2, Y1), Y2), List.append(&2, S.St, A2, List.append(&2, S.St, Y1, Y2)), LA.shb.app_assoc(A2, Y1, Y2))

# the readings of two lists of places are those of each in turn
def shh.reads_app(f: Nat, ps: List<&2, S.Piece>, L1: List<&2, S.St>, +L2: List<&2, S.St>, +base: Nat) -> {Shape.sp_reads(f, ps, List.append(&2, S.St, L1, L2), base) == List.append(&2, S.St, Shape.sp_reads(f, ps, L1, base), Shape.sp_reads(f, ps, L2, base)) : List<&2, S.St>}:
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
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_eat(u, False{}, s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Lit{u} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Lit{u} <> t, rest, base), Shape.sp_reads(1n+g, S.Lit{u} <> t, L2, base), shh.reads_app(1n+g, S.Lit{u} <> t, rest, L2, base), A, {==})
            case S.Fold{+u}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_eat(u, True{}, s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Fold{u} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Fold{u} <> t, rest, base), Shape.sp_reads(1n+g, S.Fold{u} <> t, L2, base), shh.reads_app(1n+g, S.Fold{u} <> t, rest, L2, base), A, {==})
            case S.Run{+c, +min, +max}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_run(c, min, max, s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Run{c, min, max} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Run{c, min, max} <> t, rest, base), Shape.sp_reads(1n+g, S.Run{c, min, max} <> t, L2, base), shh.reads_app(1n+g, S.Run{c, min, max} <> t, rest, L2, base), A, {==})
            case S.Cap{+i}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)), 1n+Nat.add(base, Shape.sp_ncaps(i))) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Cap{i} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Cap{i} <> t, rest, base), Shape.sp_reads(1n+g, S.Cap{i} <> t, L2, base), shh.reads_app(1n+g, S.Cap{i} <> t, rest, L2, base), A, {==})
            case S.Opt{+i}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]), Nat.add(base, Shape.sp_ncaps(i))) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Opt{i} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Opt{i} <> t, rest, base), Shape.sp_reads(1n+g, S.Opt{i} <> t, L2, base), shh.reads_app(1n+g, S.Opt{i} <> t, rest, L2, base), A, {==})
            case S.Alt{+a, +bb}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))), Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Alt{a, bb} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Alt{a, bb} <> t, rest, base), Shape.sp_reads(1n+g, S.Alt{a, bb} <> t, L2, base), shh.reads_app(1n+g, S.Alt{a, bb} <> t, rest, L2, base), A, {==})
            case S.Many{+i, +min}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Many{i, min} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Many{i, min} <> t, rest, base), Shape.sp_reads(1n+g, S.Many{i, min} <> t, L2, base), shh.reads_app(1n+g, S.Many{i, min} <> t, rest, L2, base), A, {==})
            case S.Ahead{+i, +neg}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s), Nat.add(base, Shape.sp_ncaps(i))) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Ahead{i, neg} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Ahead{i, neg} <> t, rest, base), Shape.sp_reads(1n+g, S.Ahead{i, neg} <> t, L2, base), shh.reads_app(1n+g, S.Ahead{i, neg} <> t, rest, L2, base), A, {==})
            case S.Same{+k}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_same(k, s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Same{k} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Same{k} <> t, rest, base), Shape.sp_reads(1n+g, S.Same{k} <> t, L2, base), shh.reads_app(1n+g, S.Same{k} <> t, rest, L2, base), A, {==})
            case S.Bound{}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_bound(s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Bound{} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Bound{} <> t, rest, base), Shape.sp_reads(1n+g, S.Bound{} <> t, L2, base), shh.reads_app(1n+g, S.Bound{} <> t, rest, L2, base), A, {==})
            case S.Begin{}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_begin(s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.Begin{} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.Begin{} <> t, rest, base), Shape.sp_reads(1n+g, S.Begin{} <> t, L2, base), shh.reads_app(1n+g, S.Begin{} <> t, rest, L2, base), A, {==})
            case S.End{}:
              match L1:
                case Nil{}:
                  {==}
                case +s <> +rest:
                  +A = {Shape.sp_reads(1n+g, t, Shape.sp_end(s), base) : List<&2, S.St>}
                  shh.app_step(A, Shape.sp_reads(1n+g, S.End{} <> t, List.append(&2, S.St, rest, L2), base), Shape.sp_reads(1n+g, S.End{} <> t, rest, base), Shape.sp_reads(1n+g, S.End{} <> t, L2, base), shh.reads_app(1n+g, S.End{} <> t, rest, L2, base), A, {==})

# a reading of a place of a list is a reading of the list
def shh.reads_of(+f: Nat, +ps: List<&2, S.Piece>, L: List<&2, S.St>, +z: S.St, -r: S.St, +base: Nat, hz: Shape.sp_has(z, L), hr: Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))) -> Shape.sp_has(r, Shape.sp_reads(f, ps, L, base)):
  match L:
    case Nil{}:
      match hz:
    case +c <> +t:
      match hz:
        case Inl{e}:
          %Equal.sym(List<&2, S.St>, Shape.sp_reads(f, ps, c <> t, base), List.append(&2, S.St, Shape.sp_reads(f, ps, [c], base), Shape.sp_reads(f, ps, t, base)), shh.reads_app(f, ps, [c], t, base)) : Shape.sp_has(r, _)
          %Equal.sym(S.St, c, z, e) : Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(f, ps, [_], base), Shape.sp_reads(f, ps, t, base)))
          shh.app_l(r, Shape.sp_reads(f, ps, [z], base), Shape.sp_reads(f, ps, t, base), hr)
        case Inr{k}:
          %Equal.sym(List<&2, S.St>, Shape.sp_reads(f, ps, c <> t, base), List.append(&2, S.St, Shape.sp_reads(f, ps, [c], base), Shape.sp_reads(f, ps, t, base)), shh.reads_app(f, ps, [c], t, base)) : Shape.sp_has(r, _)
          shh.app_r(r, Shape.sp_reads(f, ps, [c], base), Shape.sp_reads(f, ps, t, base), shh.reads_of(f, ps, t, z, r, base, k, hr))

# no place is in an empty list
def shh.none(-G: Type, -r: S.St, h: Shape.sp_has(r, Nil{})) -> G:
  match h:

def shh.conv(-r: S.St, -xs: List<&2, S.St>, -ys: List<&2, S.St>, e: {xs == ys : List<&2, S.St>}, h: Shape.sp_has(r, xs)) -> Shape.sp_has(r, ys):
  %e : Shape.sp_has(r, _)
  h

def shh.from.nil(+f: Nat, +ps: List<&2, S.Piece>, -r: S.St, +base: Nat, h: Shape.sp_has(r, Shape.sp_reads(f, ps, Nil{}, base))) -> &z: S.St -> (Shape.sp_has(z, Nil{}) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))):
  shh.none(&z: S.St -> (Shape.sp_has(z, Nil{}) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))), r, shh.conv(r, Shape.sp_reads(f, ps, Nil{}, base), Nil{}, shh.reads_nil(f, ps, base), h))

def shh.from.cons(+f: Nat, +ps: List<&2, S.Piece>, +c: S.St, +t: List<&2, S.St>, -r: S.St, +base: Nat, h: Shape.sp_has(r, Shape.sp_reads(f, ps, c <> t, base))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(f, ps, [c], base), Shape.sp_reads(f, ps, t, base))):
  %shh.reads_app(f, ps, [c], t, base) : Shape.sp_has(r, _)
  h

def shh.from.fin(-f: Nat, -ps: List<&2, S.Piece>, -c: S.St, -t: List<&2, S.St>, -r: S.St, -base: Nat, w: &z: S.St -> (Shape.sp_has(z, t) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base)))) -> &z: S.St -> (Shape.sp_has(z, c <> t) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))):
  (z, hp) = w
  (hz, hr) = hp
  (z, (Inr{hz}, hr))

def shh.from.go(-f: Nat, -ps: List<&2, S.Piece>, +c: S.St, -t: List<&2, S.St>, -r: S.St, -base: Nat, e: Shape.sp_has(r, Shape.sp_reads(f, ps, [c], base)) | Shape.sp_has(r, Shape.sp_reads(f, ps, t, base)), ih: Shape.sp_has(r, Shape.sp_reads(f, ps, t, base)) -> &z: S.St -> (Shape.sp_has(z, t) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base)))) -> &z: S.St -> (Shape.sp_has(z, c <> t) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))):
  match e:
    case Inl{hc}:
      (c, (Inl{{==}}, hc))
    case Inr{ht}:
      shh.from.fin(f, ps, c, t, r, base, ih(ht))

# a reading of a list is a reading of one of its places
def shh.reads_from(+f: Nat, +ps: List<&2, S.Piece>, L: List<&2, S.St>, -r: S.St, +base: Nat, h: Shape.sp_has(r, Shape.sp_reads(f, ps, L, base))) -> &z: S.St -> (Shape.sp_has(z, L) & Shape.sp_has(r, Shape.sp_reads(f, ps, [z], base))):
  match L:
    case Nil{}:
      shh.from.nil(f, ps, r, base, h)
    case +c <> +t:
      shh.from.go(f, ps, c, t, r, base, shh.app_split(r, Shape.sp_reads(f, ps, [c], base), Shape.sp_reads(f, ps, t, base), shh.from.cons(f, ps, c, t, r, base, h)), k => shh.reads_from(f, ps, t, r, base, k))

