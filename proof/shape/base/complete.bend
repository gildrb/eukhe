# eukhe: every split of the text from a place reaches one of its readings
# (laws/shape/match.bend R4, R6), by induction along Shape.sp_split: the part of
# the first piece reaches a reading z of that piece (the inner parts by
# induction), and the rest of the parts reach a reading of the rest from z.
# A Many's later rounds are read with less fuel by the spec; any fuel past
# the chars after a place reads the same (LU.shu.fi).

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./has.bend as LH
import ./fuel.bend as LU
import ./chars.bend as LQ
import ./split.bend as LP
import ./parts.bend as LR
import ./whole.bend as LN
import ./sound.bend as LS

def shc.lt0(-G: Type, +a: Nat, +ha: Nat, e: {ha == a : Nat}, h: {Nat.is_lt(a, 0n) == True{} : Bool}) -> G:
  LU.shu.absurd(G, Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, LU.shu.lt_zero(a)), h))

# a reading z of the piece, then a reading of the rest from z
def shc.fin(+R1: List<&2, S.St>, +g: Nat, +t: List<&2, S.Piece>, +b1: Nat, +z: S.St, -r: S.St, hz: Shape.sp_has(z, R1), hr: Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], b1))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, R1, b1), Nil{})):
  LH.shh.app_l(r, Shape.sp_reads(1n+g, t, R1, b1), Nil{}, LH.shh.reads_of(1n+g, t, R1, z, r, b1, hz, hr))

# Leaves
# ------

def shc.run(s: S.St, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +u: String, -z: S.St, +e: {Shape.sp_part_run(c, min, max, u, Some{s}) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_run(c, min, max, s)):
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      LP.shp.run_c(rest, c, min, max, pos, left, word, caps, u, z, e)

def shc.same(s: S.St, +k: Nat, +u: String, -z: S.St, +e: {Shape.sp_part_same(k, u, Some{s}) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_same(k, s)):
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      LN.shn.same_c(Shape.sp_took(k, caps), u, S.St{pos, left, word, rest, caps}, z, e)

# Compound pieces
# ---------------

def shc.cap_in(-G: Type, +k: Nat, +s: S.St, inn: Maybe<&2, S.St>, -z: S.St, e: {Shape.sp_part_cap(k, Some{s}, inn) == Some{z} : Maybe<&2, S.St>}, q: @x: S.St -> {inn == Some{x} : Maybe<&2, S.St>} -> {Shape.sp_head(Shape.sp_cap([x], k, Shape.sp_pos(s), Shape.sp_text(s))) == Some{z} : Maybe<&2, S.St>} -> G) -> G:
  match inn:
    case None{}:
      LP.shp.none_some(G, z, e)
    case Some{+x}:
      q(x, {==}, e)

def shc.opt(took: Bool, +s: S.St, -inn: Maybe<&2, S.St>, +xs: List<&2, S.St>, -z: S.St, +e: {Shape.sp_pick(took, inn, Some{s}) == Some{z} : Maybe<&2, S.St>}, ih: {inn == Some{z} : Maybe<&2, S.St>} -> Shape.sp_has(z, xs)) -> Shape.sp_has(z, List.append(&2, S.St, xs, [s])):
  match took:
    case True{}:
      LH.shh.app_l(z, xs, [s], ih(e))
    case False{}:
      LH.shh.app_r(z, xs, [s], Inl{LP.shp.some_inj(s, z, e)})

def shc.alt(took: Bool, -ia: Maybe<&2, S.St>, -ib: Maybe<&2, S.St>, +xa: List<&2, S.St>, -xb: List<&2, S.St>, -z: S.St, e: {Shape.sp_pick(took, ia, ib) == Some{z} : Maybe<&2, S.St>}, iha: {ia == Some{z} : Maybe<&2, S.St>} -> Shape.sp_has(z, xa), ihb: {ib == Some{z} : Maybe<&2, S.St>} -> Shape.sp_has(z, xb)) -> Shape.sp_has(z, List.append(&2, S.St, xa, xb)):
  match took:
    case True{}:
      LH.shh.app_l(z, xa, xb, iha(e))
    case False{}:
      LH.shh.app_r(z, xa, xb, ihb(e))

def shc.ahead.pos(-inn: Maybe<&2, S.St>, +xs: List<&2, S.St>, +s: S.St, -z: S.St, sy: &y: S.St -> {inn == Some{y} : Maybe<&2, S.St>}, ih: @y: S.St -> {inn == Some{y} : Maybe<&2, S.St>} -> Shape.sp_has(y, xs)) -> Shape.sp_has(s, Shape.sp_ahead(False{}, xs, s)):
  (+y, ey) = sy
  LN.shn.ahead_in(False{}, xs, s, y, ih(y, ey), {==})

def shc.ahead(neg: Bool, +g: Nat, +i: List<&2, S.Piece>, +s: S.St, +base: Nat, +inn: Maybe<&2, S.St>, -z: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +e: {Shape.sp_part_ahead(neg, inn, i, base, Some{s}) == Some{z} : Maybe<&2, S.St>}, ih: @y: S.St -> {inn == Some{y} : Maybe<&2, S.St>} -> Shape.sp_has(y, Shape.sp_reads(1n+g, i, [s], base))) -> Shape.sp_has(z, Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s)):
  match neg:
    case False{}:
      +ez = {LP.shp.some_inj(s, z, LP.shp.when_m(Shape.sp_some(inn), Some{s}, z, e)) : {s == z : S.St}}
      %ez : Shape.sp_has(_, Shape.sp_ahead(False{}, Shape.sp_reads(1n+g, i, [s], base), s))
      shc.ahead.pos(inn, Shape.sp_reads(1n+g, i, [s], base), s, z, LN.shn.some_of(inn, z, LP.shp.when_t(Shape.sp_some(inn), Some{s}, z, e)), ih)
    case True{}:
      +xa = {Shape.sp_reads(1n+Shape.sp_left(s), i, [s], base) : List<&2, S.St>}
      +ez = {LP.shp.some_inj(s, z, LP.shp.when_m(List.is_empty(&2, S.St, xa), Some{s}, z, e)) : {s == z : S.St}}
      +en = {LN.shn.is_empty(xa, LP.shp.when_t(List.is_empty(&2, S.St, xa), Some{s}, z, e)) : {xa == Nil{} : List<&2, S.St>}}
      +e1 = {LU.shu.fi(1n+g, 1n+Shape.sp_left(s), i, [s], base, LU.shu.one(1n+g, s, hf), LU.shu.one(1n+Shape.sp_left(s), s, LS.shs.lt_self(Shape.sp_left(s)))) : {Shape.sp_reads(1n+g, i, [s], base) == xa : List<&2, S.St>}}
      %ez : Shape.sp_has(_, Shape.sp_ahead(True{}, Shape.sp_reads(1n+g, i, [s], base), s))
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(1n+g, i, [s], base), Nil{}, Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g, i, [s], base), xa, Nil{}, e1, en)) : Shape.sp_has(s, Shape.sp_ahead(True{}, _, s))
      Inl{{==}}

# Many
# ----

def shc.many.z(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +y: S.St, +hyx: Shape.sp_has(y, Shape.sp_reads(1n+g, i, [s], base)), +hl: {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}, sz: &z: S.St -> (Shape.sp_has(z, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(Shape.sp_dec(min))}], Shape.sp_moved(Shape.sp_left(y), Shape.sp_reads(1n+g, i, [y], base)), base), Shape.sp_zero(Shape.sp_dec(min), y))) & Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], Nat.add(base, Shape.sp_ncaps(i)))))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})):
  (+z, q) = sz
  (hz, hrz) = q
  +fyg = {LU.shu.lt_lt(Shape.sp_left(y), Shape.sp_left(s), g, hl, hf) : {Nat.is_lt(Shape.sp_left(y), g) == True{} : Bool}}
  +e = {LU.shu.fi(1n+g, g, [S.Many{i, Shape.sp_dec(min)}], [y], base, LU.shu.one(1n+g, y, LU.shu.lt_succ(Shape.sp_left(y), g, fyg)), LU.shu.one(g, y, fyg)) : {Shape.sp_reads(1n+g, [S.Many{i, Shape.sp_dec(min)}], [y], base) == Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base) : List<&2, S.St>}}
  +hz2 = {LH.shh.conv(z, Shape.sp_reads(1n+g, [S.Many{i, Shape.sp_dec(min)}], [y], base), Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base), e, LH.shh.app_l(z, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(Shape.sp_dec(min))}], Shape.sp_moved(Shape.sp_left(y), Shape.sp_reads(1n+g, i, [y], base)), base), Shape.sp_zero(Shape.sp_dec(min), y)), Nil{}, hz)) : Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base))}
  +hz3 = {LH.shh.reads_of(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), y, z, base, LR.shr.moved_in(y, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), hyx, hl), hz2) : Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base))}
  shc.fin(List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), g, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, LH.shh.app_l(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), hz3), hrz)

def shc.many.y(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +y: S.St, +hyx: Shape.sp_has(y, Shape.sp_reads(1n+g, i, [s], base)), +hl: {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}, hr: Shape.sp_has(r, Shape.sp_reads(1n+g, S.Many{i, Shape.sp_dec(min)} <> t, [y], base))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})):
  shc.many.z(g, i, min, t, s, base, r, hf, y, hyx, hl, LH.shh.reads_from(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(Shape.sp_dec(min))}], Shape.sp_moved(Shape.sp_left(y), Shape.sp_reads(1n+g, i, [y], base)), base), Shape.sp_zero(Shape.sp_dec(min), y)), r, Nat.add(base, Shape.sp_ncaps(i)), LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(Shape.sp_dec(min))}], Shape.sp_moved(Shape.sp_left(y), Shape.sp_reads(1n+g, i, [y], base)), base), Shape.sp_zero(Shape.sp_dec(min), y)), Nat.add(base, Shape.sp_ncaps(i))), hr)))

def shc.many.stop(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +z: S.St, +ez: {Shape.sp_part_stop(min, Some{s}) == Some{z} : Maybe<&2, S.St>}, ih: {Nat.is_lt(Shape.sp_left(z), 1n+g) == True{} : Bool} -> Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], Nat.add(base, Shape.sp_ncaps(i))))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})):
  +em = {LN.shn.stop_min(min, Some{s}, z, ez) : {min == 0n : Nat}}
  +es = {LP.shp.some_inj(s, z, LN.shn.stop_m(min, Some{s}, z, ez)) : {s == z : S.St}}
  +h0 = {LP.shp.run_c.zero(min, s, z, em, es) : Shape.sp_has(z, Shape.sp_zero(min, s))}
  +hz = {LH.shh.app_r(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), h0) : Shape.sp_has(z, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)))}
  shc.fin(List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), g, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, hz, ih(LR.shr.has_fits(z, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), 1n+g, hz, LU.shu.fits_app(1n+g, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), LU.shu.pf(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base, 1n+g, LU.shu.moved(1n+g, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), LU.shu.pf(1n+g, i, [s], base, 1n+g, LU.shu.one(1n+g, s, hf)))), LU.shu.zero(min, 1n+g, s, hf)))))

def shc.many(took: Bool, +g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +wt: List<&2, Shape.Part>, +wi: List<&2, Shape.Part>, h: {Shape.sp_pick(took, Shape.sp_split(wt, S.Many{i, Shape.sp_dec(min)} <> t, base, Shape.sp_part_round(Some{s}, Shape.sp_split(wi, i, base, Some{s}))), Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_stop(min, Some{s}))) == Some{r} : Maybe<&2, S.St>}, ih_i: @y: S.St -> {Shape.sp_split(wi, i, base, Some{s}) == Some{y} : Maybe<&2, S.St>} -> Shape.sp_has(y, Shape.sp_reads(1n+g, i, [s], base)), ih_m: @y: S.St -> {Nat.is_lt(Shape.sp_left(y), 1n+g) == True{} : Bool} -> {Shape.sp_split(wt, S.Many{i, Shape.sp_dec(min)} <> t, base, Some{y}) == Some{r} : Maybe<&2, S.St>} -> Shape.sp_has(r, Shape.sp_reads(1n+g, S.Many{i, Shape.sp_dec(min)} <> t, [y], base)), ih_t: @z: S.St -> {Nat.is_lt(Shape.sp_left(z), 1n+g) == True{} : Bool} -> {Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>} -> Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], Nat.add(base, Shape.sp_ncaps(i))))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})):
  match took:
    case True{}:
      +inn = {Shape.sp_split(wi, i, base, Some{s}) : Maybe<&2, S.St>}
      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})), wt, S.Many{i, Shape.sp_dec(min)} <> t, base, Shape.sp_part_round(Some{s}, inn), r, h, +y => +ey => hy => shc.many.y(g, i, min, t, s, base, r, hf, y, ih_i(y, LN.shn.round_m(s, inn, y, ey)), LN.shn.round_lt(s, inn, y, ey), ih_m(y, LU.shu.lt_succ(Shape.sp_left(y), g, LU.shu.lt_lt(Shape.sp_left(y), Shape.sp_left(s), g, LN.shn.round_lt(s, inn, y, ey), hf)), hy)))
    case False{}:
      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)), Nat.add(base, Shape.sp_ncaps(i))), Nil{})), wt, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_stop(min, Some{s}), r, h, +z => +ez => hz => shc.many.stop(g, i, min, t, s, base, r, hf, z, ez, fz => ih_t(z, fz, hz)))

# a leaf's reading z, then the rest by induction
def shc.leaf(+R1: List<&2, S.St>, +g: Nat, +t: List<&2, S.Piece>, +b1: Nat, +z: S.St, -r: S.St, +hz: Shape.sp_has(z, R1), +fr: {LU.shu.fits(1n+g, R1) == True{} : Bool}, ih: {Nat.is_lt(Shape.sp_left(z), 1n+g) == True{} : Bool} -> Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], b1))) -> Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, R1, b1), Nil{})):
  shc.fin(R1, g, t, b1, z, r, hz, ih(LR.shr.has_fits(z, R1, 1n+g, hz, fr)))

# every split from a place, fuel past its chars, reaches a reading
def shc.complete(ws: List<&2, Shape.Part>, ps: List<&2, S.Piece>, +base: Nat, +s: S.St, -r: S.St, +f: Nat, +hf: {Nat.is_lt(Shape.sp_left(s), f) == True{} : Bool}, +h: {Shape.sp_split(ws, ps, base, Some{s}) == Some{r} : Maybe<&2, S.St>}) -> Shape.sp_has(r, Shape.sp_reads(f, ps, [s], base)):
  match ws:
    case Nil{}:
      match ps:
        case Nil{}:
          match f:
            case 0n:
              shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, Nil{}, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
            case 1n++g:
              Inl{LP.shp.some_inj(s, r, h)}
        case p <> t:
          LP.shp.none_some(Shape.sp_has(r, Shape.sp_reads(f, p <> t, [s], base)), r, h)
    case w <> +wt:
      match w:
        case Shape.Part{+took, +u, +wi}:
          match ps:
            case Nil{}:
              LP.shp.none_some(Shape.sp_has(r, Shape.sp_reads(f, Nil{}, [s], base)), r, h)
            case p <> +t:
              match p:
                case S.Lit{+v}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Lit{v} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_eat(v, False{}, s), base), Nil{})), wt, t, base, Shape.sp_when(Shape.sp_text_eq(False{}, u, v), Shape.sp_go_on(u, Some{s})), r, h, +z => +ez => hz => shc.leaf(Shape.sp_eat(v, False{}, s), g, t, base, z, r, LP.shp.lit_c(u, v, s, z, ez), LU.shu.eat(v, False{}, s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Fold{+v}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Fold{v} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_eat(v, True{}, s), base), Nil{})), wt, t, base, Shape.sp_when(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s})), r, h, +z => +ez => hz => shc.leaf(Shape.sp_eat(v, True{}, s), g, t, base, z, r, LP.shp.fold_c(u, v, s, z, LP.shp.when_t(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s}), z, ez), LP.shp.when_m(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s}), z, ez)), LU.shu.eat(v, True{}, s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Run{+c, +min, +max}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Run{c, min, max} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_run(c, min, max, s), base), Nil{})), wt, t, base, Shape.sp_part_run(c, min, max, u, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_run(c, min, max, s), g, t, base, z, r, shc.run(s, c, min, max, u, z, ez), LU.shu.run(c, min, max, s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Same{+k}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Same{k} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_same(k, s), base), Nil{})), wt, t, base, Shape.sp_part_same(k, u, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_same(k, s), g, t, base, z, r, shc.same(s, k, u, z, ez), LU.shu.same(k, s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Bound{}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Bound{} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_bound(s), base), Nil{})), wt, t, base, Shape.sp_part_bound(u, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_bound(s), g, t, base, z, r, LP.shp.head_has(Shape.sp_bound(s), z, LP.shp.when_m(String.is_empty(u), Shape.sp_head(Shape.sp_bound(s)), z, ez)), LU.shu.bound(s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Begin{}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Begin{} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_begin(s), base), Nil{})), wt, t, base, Shape.sp_part_begin(u, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_begin(s), g, t, base, z, r, LP.shp.head_has(Shape.sp_begin(s), z, LP.shp.when_m(String.is_empty(u), Shape.sp_head(Shape.sp_begin(s)), z, ez)), LU.shu.begin(s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.End{}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.End{} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_end(s), base), Nil{})), wt, t, base, Shape.sp_part_end(u, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_end(s), g, t, base, z, r, LP.shp.head_has(Shape.sp_end(s), z, LP.shp.when_m(String.is_empty(u), Shape.sp_head(Shape.sp_end(s)), z, ez)), LU.shu.end(s, 1n+g, hf), fz => shc.complete(wt, t, base, z, r, 1n+g, fz, hz)))
                case S.Cap{+i}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Cap{i} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)), 1n+Nat.add(base, Shape.sp_ncaps(i))), Nil{})), wt, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_cap(base, Some{s}, Shape.sp_split(wi, i, 1n+base, Some{s})), r, h, +z => +ez => hz => shc.cap_in(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)), 1n+Nat.add(base, Shape.sp_ncaps(i))), Nil{})), base, s, Shape.sp_split(wi, i, 1n+base, Some{s}), z, ez, +x => +ex => +ec => shc.leaf(Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)), g, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), z, r, LR.shr.cap_has(x, z, Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), shc.complete(wi, i, 1n+base, s, x, 1n+g, hf, ex), ec), LU.shu.cap_t(1n+g, Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), LU.shu.pf(1n+g, i, [s], 1n+base, 1n+g, LU.shu.one(1n+g, s, hf))), fz => shc.complete(wt, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), z, r, 1n+g, fz, hz))))
                case S.Opt{+i}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Opt{i} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]), Nat.add(base, Shape.sp_ncaps(i))), Nil{})), wt, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_pick(took, Shape.sp_split(wi, i, base, Some{s}), Some{s}), r, h, +z => +ez => hz => shc.leaf(List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]), g, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, shc.opt(took, s, Shape.sp_split(wi, i, base, Some{s}), Shape.sp_reads(1n+g, i, [s], base), z, ez, ei => shc.complete(wi, i, base, s, z, 1n+g, hf, ei)), LU.shu.fits_app(1n+g, Shape.sp_reads(1n+g, i, [s], base), [s], LU.shu.pf(1n+g, i, [s], base, 1n+g, LU.shu.one(1n+g, s, hf)), LU.shu.one(1n+g, s, hf)), fz => shc.complete(wt, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, 1n+g, fz, hz)))
                case S.Alt{+a, +bb}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Alt{a, bb} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))), Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb))), Nil{})), wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Shape.sp_pick(took, Shape.sp_split(wi, a, base, Some{s}), Shape.sp_split(wi, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s})), r, h, +z => +ez => hz => shc.leaf(List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))), g, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), z, r, shc.alt(took, Shape.sp_split(wi, a, base, Some{s}), Shape.sp_split(wi, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s}), Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), z, ez, ea => shc.complete(wi, a, base, s, z, 1n+g, hf, ea), eb => shc.complete(wi, bb, Nat.add(base, Shape.sp_ncaps(a)), s, z, 1n+g, hf, eb)), LU.shu.fits_app(1n+g, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), LU.shu.pf(1n+g, a, [s], base, 1n+g, LU.shu.one(1n+g, s, hf)), LU.shu.pf(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), 1n+g, LU.shu.one(1n+g, s, hf))), fz => shc.complete(wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), z, r, 1n+g, fz, hz)))
                case S.Ahead{+i, +neg}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Ahead{i, neg} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      LN.shn.bind(Shape.sp_has(r, List.append(&2, S.St, Shape.sp_reads(1n+g, t, Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s), Nat.add(base, Shape.sp_ncaps(i))), Nil{})), wt, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_ahead(neg, Shape.sp_split(wi, i, base, Some{s}), i, base, Some{s}), r, h, +z => +ez => hz => shc.leaf(Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s), g, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, shc.ahead(neg, g, i, s, base, Shape.sp_split(wi, i, base, Some{s}), z, hf, ez, y => ey => shc.complete(wi, i, base, s, y, 1n+g, hf, ey)), LU.shu.ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s, 1n+g, hf), fz => shc.complete(wt, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, 1n+g, fz, hz)))
                case S.Many{+i, +min}:
                  match f:
                    case 0n:
                      shc.lt0(Shape.sp_has(r, Shape.sp_reads(0n, S.Many{i, min} <> t, [s], base)), Shape.sp_left(s), Shape.sp_left(s), {==}, hf)
                    case 1n++g:
                      shc.many(took, g, i, min, t, s, base, r, hf, wt, wi, h, y => ey => shc.complete(wi, i, base, s, y, 1n+g, hf, ey), y => fy => hy => shc.complete(wt, S.Many{i, Shape.sp_dec(min)} <> t, base, y, r, 1n+g, fy, hy), z => fz => hz => shc.complete(wt, t, Nat.add(base, Shape.sp_ncaps(i)), z, r, 1n+g, fz, hz))

