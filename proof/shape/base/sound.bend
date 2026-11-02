# eukhe: every reading of a place is a split (laws/shape/match.bend R4, R6), by
# induction along Shape.sp_reads: a reading of p then t is a reading z of
# p (one part, or a Many's parts) then a reading of t from z (its parts by
# induction).

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

def shs.lt_self(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      shs.lt_self(p)

# the rest of the parts after one part that reaches z
def shs.then(-ws: List<&2, Shape.Part>, -t: List<&2, S.Piece>, -b: Nat, -m: Maybe<&2, S.St>, -z: S.St, -r: S.St, em: {m == Some{z} : Maybe<&2, S.St>}, et: {Shape.sp_split(ws, t, b, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> {Shape.sp_split(ws, t, b, m) == Some{r} : Maybe<&2, S.St>}:
  %Equal.sym(Maybe<&2, S.St>, m, Some{z}, em) : {Shape.sp_split(ws, t, b, _) == Some{r} : Maybe<&2, S.St>}
  et

# a reading z of the piece, then the parts of the rest from z
def shs.go(-G: Type, +R1: List<&2, S.St>, +g: Nat, -t: List<&2, S.Piece>, -B: Nat, -r: S.St, w: &z: S.St -> (Shape.sp_has(z, R1) & Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], B))), +fr: {LU.shu.fits(1n+g, R1) == True{} : Bool}, ih_t: @z: S.St -> {Nat.is_lt(Shape.sp_left(z), 1n+g) == True{} : Bool} -> Shape.sp_has(r, Shape.sp_reads(1n+g, t, [z], B)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, B, Some{z}) == Some{r} : Maybe<&2, S.St>}, k: @z: S.St -> Shape.sp_has(z, R1) -> (&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, B, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> G) -> G:
  (+z, q) = w
  (+hz, hr) = q
  k(z, hz, ih_t(z, LR.shr.has_fits(z, R1, 1n+g, hz, fr), hr))

# Leaves
# ------

def shs.lit(+v: String, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_eat(v, False{}, s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Lit{v} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{True{}, v, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_when(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s})), z, r, LP.shp.lit_s(v, s, z, hz), et))

def shs.fold.fin(+v: String, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, su: &u: String -> ({Shape.sp_text_eq(True{}, u, v) == True{} : Bool} & {Shape.sp_head(Shape.sp_eat(u, False{}, s)) == Some{z} : Maybe<&2, S.St>}), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Fold{v} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+u, q) = su
  (e1, e2) = q
  (+ws, et) = wt
  (Shape.Part{True{}, u, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_when(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s})), z, r, Equal.trans(Maybe<&2, S.St>, Shape.sp_when(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s})), Shape.sp_go_on(u, Some{s}), Some{z}, LP.shp.when_true(Shape.sp_text_eq(True{}, u, v), Shape.sp_go_on(u, Some{s}), e1), e2), et))

def shs.fold(+v: String, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_eat(v, True{}, s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Fold{v} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  shs.fold.fin(v, t, s, base, r, z, LP.shp.fold_s(v, s, z, hz), wt)

def shs.run.fin(+c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +t: List<&2, S.Piece>, +st: S.St, +base: Nat, -r: S.St, +z: S.St, su: &u: String -> {Shape.sp_part_run(c, min, max, u, Some{st}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Run{c, min, max} <> t, base, Some{st}) == Some{r} : Maybe<&2, S.St>}:
  (+u, e) = su
  (+ws, et) = wt
  (Shape.Part{True{}, u, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_part_run(c, min, max, u, Some{st}), z, r, e, et))

def shs.run(+c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +t: List<&2, S.Piece>, s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_run(c, min, max, s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Run{c, min, max} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shs.run.fin(c, min, max, t, S.St{pos, left, word, rest, caps}, base, r, z, LP.shp.run_s(rest, c, min, max, pos, left, word, caps, z, hz), wt)

def shs.same.fin(+k: Nat, +t: List<&2, S.Piece>, +st: S.St, +base: Nat, -r: S.St, +z: S.St, su: &u: String -> {Shape.sp_when(Shape.sp_is(Shape.sp_took(k, Shape.sp_caps(st)), u), Shape.sp_go_on(u, Some{st})) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Same{k} <> t, base, Some{st}) == Some{r} : Maybe<&2, S.St>}:
  (+u, e) = su
  (+ws, et) = wt
  (Shape.Part{True{}, u, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_part_same(k, u, Some{st}), z, r, e, et))

def shs.same(+k: Nat, +t: List<&2, S.Piece>, s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_same(k, s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Same{k} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shs.same.fin(k, t, S.St{pos, left, word, rest, caps}, base, r, z, LN.shn.same_s(Shape.sp_took(k, caps), S.St{pos, left, word, rest, caps}, z, hz), wt)

def shs.bound.fin(+t: List<&2, S.Piece>, +st: S.St, +base: Nat, -r: S.St, -z: S.St, e: {Shape.sp_head(Shape.sp_bound(st)) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Bound{} <> t, base, Some{st}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{True{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_part_bound(SNil{}, Some{st}), z, r, e, et))

def shs.bound(+t: List<&2, S.Piece>, s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_bound(s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Bound{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shs.bound.fin(t, S.St{pos, left, word, rest, caps}, base, r, z, LN.shn.one_head(Bool.xor(word, Shape.sp_starts_word(rest)), S.St{pos, left, word, rest, caps}, z, hz), wt)

def shs.begin.fin(+t: List<&2, S.Piece>, +st: S.St, +base: Nat, -r: S.St, -z: S.St, e: {Shape.sp_head(Shape.sp_begin(st)) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Begin{} <> t, base, Some{st}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{True{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_part_begin(SNil{}, Some{st}), z, r, e, et))

def shs.begin(+t: List<&2, S.Piece>, s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_begin(s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Begin{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shs.begin.fin(t, S.St{pos, left, word, rest, caps}, base, r, z, LN.shn.one_head(Nat.is_eq(pos, 0n), S.St{pos, left, word, rest, caps}, z, hz), wt)

def shs.end.fin(+t: List<&2, S.Piece>, +st: S.St, +base: Nat, -r: S.St, -z: S.St, e: {Shape.sp_head(Shape.sp_end(st)) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.End{} <> t, base, Some{st}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{True{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, base, Shape.sp_part_end(SNil{}, Some{st}), z, r, e, et))

def shs.end(+t: List<&2, S.Piece>, s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_end(s)), wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, base, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.End{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shs.end.fin(t, S.St{pos, left, word, rest, caps}, base, r, z, LN.shn.one_head(String.is_empty(rest), S.St{pos, left, word, rest, caps}, z, hz), wt)

# Compound pieces
# ---------------

def shs.cap.b(+i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -x: S.St, +z: S.St, ex: {Shape.sp_head(Shape.sp_cap([x], base, Shape.sp_pos(s), Shape.sp_text(s))) == Some{z} : Maybe<&2, S.St>}, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, 1n+base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Cap{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+ws, et) = wt
  +inn = {Shape.sp_split(wsi, i, 1n+base, Some{s}) : Maybe<&2, S.St>}
  (Shape.Part{True{}, SNil{}, wsi} <> ws, shs.then(ws, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_cap(base, Some{s}, inn), z, r, Equal.trans(Maybe<&2, S.St>, Shape.sp_part_cap(base, Some{s}, inn), Shape.sp_part_cap(base, Some{s}, Some{x}), Some{z}, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.St>, m => Shape.sp_part_cap(base, Some{s}, m), inn, Some{x}, ei), ex), et))

def shs.cap.a(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, cx: &x: S.St -> (Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], 1n+base)) & {Shape.sp_head(Shape.sp_cap([x], base, Shape.sp_pos(s), Shape.sp_text(s))) == Some{z} : Maybe<&2, S.St>}), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], 1n+base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, 1n+base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Cap{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+x, q) = cx
  (hx, ex) = q
  shs.cap.b(i, t, s, base, r, x, z, ex, ih_i(x, hx), wt)

def shs.cap(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s))), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], 1n+base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, 1n+base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, 1n+Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Cap{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  shs.cap.a(g, i, t, s, base, r, z, LR.shr.cap_from(z, Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), hz), ih_i, wt)

def shs.opt.in(+i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Opt{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+ws, et) = wt
  (Shape.Part{True{}, SNil{}, wsi} <> ws, shs.then(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_pick(True{}, Shape.sp_split(wsi, i, base, Some{s}), Some{s}), z, r, ei, et))

def shs.opt.out(+i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, ez: {s == z : S.St}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Opt{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{False{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{s}, z, r, Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, s, z, ez), et))

def shs.opt.go(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, e: Shape.sp_has(z, Shape.sp_reads(1n+g, i, [s], base)) | Shape.sp_has(z, [s]), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Opt{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match e:
    case Inl{hx}:
      shs.opt.in(i, t, s, base, r, z, ih_i(z, hx), wt)
    case Inr{hs}:
      shs.opt.out(i, t, s, base, r, z, LH.shh.single(z, s, hs), wt)

def shs.opt(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s])), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Opt{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  shs.opt.go(g, i, t, s, base, r, z, LH.shh.app_split(z, Shape.sp_reads(1n+g, i, [s], base), [s], hz), ih_i, wt)

def shs.alt.a(+a: List<&2, S.Piece>, +bb: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, a, base, Some{s}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Alt{a, bb} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+ws, et) = wt
  (Shape.Part{True{}, SNil{}, wsi} <> ws, shs.then(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Shape.sp_pick(True{}, Shape.sp_split(wsi, a, base, Some{s}), Shape.sp_split(wsi, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s})), z, r, ei, et))

def shs.alt.b(+a: List<&2, S.Piece>, +bb: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Alt{a, bb} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+ws, et) = wt
  (Shape.Part{False{}, SNil{}, wsi} <> ws, shs.then(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Shape.sp_pick(False{}, Shape.sp_split(wsi, a, base, Some{s}), Shape.sp_split(wsi, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s})), z, r, ei, et))

def shs.alt.go(+g: Nat, +a: List<&2, S.Piece>, +bb: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, e: Shape.sp_has(z, Shape.sp_reads(1n+g, a, [s], base)) | Shape.sp_has(z, Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))), ih_a: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, a, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, a, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, ih_b: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Alt{a, bb} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match e:
    case Inl{ha}:
      shs.alt.a(a, bb, t, s, base, r, z, ih_a(z, ha), wt)
    case Inr{hb}:
      shs.alt.b(a, bb, t, s, base, r, z, ih_b(z, hb), wt)

def shs.alt(+g: Nat, +a: List<&2, S.Piece>, +bb: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hz: Shape.sp_has(z, List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))))), ih_a: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, a, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, a, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, ih_b: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, bb, Nat.add(base, Shape.sp_ncaps(a)), Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Alt{a, bb} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  shs.alt.go(g, a, bb, t, s, base, r, z, LH.shh.app_split(z, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), hz), ih_a, ih_b, wt)

def shs.conv_sig(-t: List<&2, S.Piece>, -b: Nat, -r: S.St, -z: S.St, -s: S.St, e: {s == z : S.St}, w: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, b, Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, b, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  %Equal.sym(S.St, s, z, e) : &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, b, Some{_}) == Some{r} : Maybe<&2, S.St>}
  w

def shs.ahead.pos.fin(+i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -y: S.St, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{y} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{s}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Ahead{i, False{}} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+ws, et) = wt
  +inn = {Shape.sp_split(wsi, i, base, Some{s}) : Maybe<&2, S.St>}
  (Shape.Part{True{}, SNil{}, wsi} <> ws, shs.then(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_ahead(False{}, inn, i, base, Some{s}), s, r, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.St>, m => Shape.sp_part_ahead(False{}, m, i, base, Some{s}), inn, Some{y}, ei), et))

def shs.ahead.pos(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, sy: &y: S.St -> Shape.sp_has(y, Shape.sp_reads(1n+g, i, [s], base)), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{s}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Ahead{i, False{}} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+y, hy) = sy
  shs.ahead.pos.fin(i, t, s, base, r, y, ih_i(y, hy), wt)

def shs.ahead.neg(+g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, en: {Shape.sp_reads(1n+g, i, [s], base) == Nil{} : List<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{s}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Ahead{i, True{}} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  +xa = {Shape.sp_reads(1n+Shape.sp_left(s), i, [s], base) : List<&2, S.St>}
  +e1 = {LU.shu.fi(1n+Shape.sp_left(s), 1n+g, i, [s], base, LU.shu.one(1n+Shape.sp_left(s), s, shs.lt_self(Shape.sp_left(s))), LU.shu.one(1n+g, s, hf)) : {xa == Shape.sp_reads(1n+g, i, [s], base) : List<&2, S.St>}}
  (Shape.Part{True{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_ahead(True{}, Shape.sp_split(Nil{}, i, base, Some{s}), i, base, Some{s}), s, r, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, xs => Shape.sp_when(List.is_empty(&2, S.St, xs), Some{s}), xa, Nil{}, Equal.trans(List<&2, S.St>, xa, Shape.sp_reads(1n+g, i, [s], base), Nil{}, e1, en)), et))

def shs.ahead(neg: Bool, +g: Nat, +i: List<&2, S.Piece>, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +z: S.St, +hz: Shape.sp_has(z, Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s)), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Ahead{i, neg} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match neg:
    case False{}:
      +ez = {LN.shn.ahead_is(False{}, Shape.sp_reads(1n+g, i, [s], base), s, z, hz) : {s == z : S.St}}
      shs.ahead.pos(g, i, t, s, base, r, LN.shn.ahead_pos(Shape.sp_reads(1n+g, i, [s], base), s, z, hz), ih_i, shs.conv_sig(t, Nat.add(base, Shape.sp_ncaps(i)), r, z, s, ez, wt))
    case True{}:
      +ez = {LN.shn.ahead_is(True{}, Shape.sp_reads(1n+g, i, [s], base), s, z, hz) : {s == z : S.St}}
      shs.ahead.neg(g, i, t, s, base, r, hf, LN.shn.ahead_neg(Shape.sp_reads(1n+g, i, [s], base), s, z, hz), shs.conv_sig(t, Nat.add(base, Shape.sp_ncaps(i)), r, z, s, ez, wt))

def shs.many.fin(+i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +y: S.St, -z: S.St, +hl: {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}, wi: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{y} : Maybe<&2, S.St>}, wm: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, [S.Many{i, Shape.sp_dec(min)}], base, Some{y}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+wsi, ei) = wi
  (+wsm, em) = wm
  (+ws, et) = wt
  +inn = {Shape.sp_split(wsi, i, base, Some{s}) : Maybe<&2, S.St>}
  +rd = {Shape.sp_part_round(Some{s}, inn) : Maybe<&2, S.St>}
  +wa = {List.append(&2, Shape.Part, wsm, ws) : List<&2, Shape.Part>}
  (Shape.Part{True{}, SNil{}, wsi} <> wa, Equal.trans(Maybe<&2, S.St>, Shape.sp_split(wa, S.Many{i, Shape.sp_dec(min)} <> t, base, rd), Shape.sp_split(wa, S.Many{i, Shape.sp_dec(min)} <> t, base, Some{y}), Some{r}, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.St>, m => Shape.sp_split(wa, S.Many{i, Shape.sp_dec(min)} <> t, base, m), rd, Some{y}, LN.shn.round_in(s, inn, y, ei, hl)), Equal.trans(Maybe<&2, S.St>, Shape.sp_split(wa, S.Many{i, Shape.sp_dec(min)} <> t, base, Some{y}), Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}), Some{r}, LN.shn.many_app(wsm, i, Shape.sp_dec(min), t, base, Some{y}, z, ws, em), et)))

def shs.many.zero(+i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, emin: {min == 0n : Nat}, ez: {s == z : S.St}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+ws, et) = wt
  (Shape.Part{False{}, SNil{}, Nil{}} <> ws, shs.then(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_part_stop(min, Some{s}), z, r, Equal.trans(Maybe<&2, S.St>, Shape.sp_part_stop(min, Some{s}), Some{s}, Some{z}, Equal.cong(Nat, Maybe<&2, S.St>, n => Shape.sp_part_stop(n, Some{s}), min, 0n, emin), Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, s, z, ez)), et))

def shs.many.a(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, -z: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, sy: &y: S.St -> (Shape.sp_has(y, Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base))) & Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base))), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, ih_m: @y: S.St -> {Nat.is_lt(Shape.sp_left(y), g) == True{} : Bool} -> Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, [S.Many{i, Shape.sp_dec(min)}], base, Some{y}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  (+y, q) = sy
  (+hy, hzm) = q
  +hl = {LR.shr.moved_lt(y, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), hy) : {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}}
  shs.many.fin(i, min, t, s, base, r, y, z, hl, ih_i(y, LR.shr.moved_has(y, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), hy)), ih_m(y, LU.shu.lt_lt(Shape.sp_left(y), Shape.sp_left(s), g, hl, hf), hzm), wt)

def shs.many.go(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +z: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, e: Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base)) | Shape.sp_has(z, Shape.sp_zero(min, s)), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, ih_m: @y: S.St -> {Nat.is_lt(Shape.sp_left(y), g) == True{} : Bool} -> Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, [S.Many{i, Shape.sp_dec(min)}], base, Some{y}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match e:
    case Inl{hm}:
      shs.many.a(g, i, min, t, s, base, r, z, hf, LH.shh.reads_from(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), z, base, hm), ih_i, ih_m, wt)
    case Inr{+h0}:
      shs.many.zero(i, min, t, s, base, r, z, LP.shp.zero_min(min, s, z, h0), LP.shp.zero_is(min, s, z, h0), wt)

def shs.many(+g: Nat, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}, +z: S.St, +hz: Shape.sp_has(z, List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s))), ih_i: @x: S.St -> Shape.sp_has(x, Shape.sp_reads(1n+g, i, [s], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, i, base, Some{s}) == Some{x} : Maybe<&2, S.St>}, ih_m: @y: S.St -> {Nat.is_lt(Shape.sp_left(y), g) == True{} : Bool} -> Shape.sp_has(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], [y], base)) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, [S.Many{i, Shape.sp_dec(min)}], base, Some{y}) == Some{z} : Maybe<&2, S.St>}, wt: &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, t, Nat.add(base, Shape.sp_ncaps(i)), Some{z}) == Some{r} : Maybe<&2, S.St>}) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  shs.many.go(g, i, min, t, s, base, r, z, hf, LH.shh.app_split(z, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), hz), ih_i, ih_m, wt)

# every reading of a place, fuel past its chars, is a split
def shs.sound(f: Nat, ps: List<&2, S.Piece>, +s: S.St, +base: Nat, -r: S.St, +hf: {Nat.is_lt(Shape.sp_left(s), f) == True{} : Bool}, h: Shape.sp_has(r, Shape.sp_reads(f, ps, [s], base))) -> &ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, ps, base, Some{s}) == Some{r} : Maybe<&2, S.St>}:
  match f:
    case 0n:
      match h:
    case 1n++g:
      match ps:
        case Nil{}:
          (Nil{}, Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, s, r, LH.shh.single(r, s, h)))
        case p <> +t:
          match p:
            case S.Lit{+u}:
              +r1 = {Shape.sp_eat(u, False{}, s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Lit{u} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.eat(u, False{}, s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.lit(u, t, s, base, r, z, hz, wt))
            case S.Fold{+u}:
              +r1 = {Shape.sp_eat(u, True{}, s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Fold{u} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.eat(u, True{}, s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.fold(u, t, s, base, r, z, hz, wt))
            case S.Run{+c, +min, +max}:
              +r1 = {Shape.sp_run(c, min, max, s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Run{c, min, max} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.run(c, min, max, s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.run(c, min, max, t, s, base, r, z, hz, wt))
            case S.Cap{+i}:
              +r1 = {Shape.sp_cap(Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
              +b1 = {1n+Nat.add(base, Shape.sp_ncaps(i)) : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Cap{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.cap_t(1n+g, Shape.sp_reads(1n+g, i, [s], 1n+base), base, Shape.sp_pos(s), Shape.sp_text(s), LU.shu.pf(1n+g, i, [s], 1n+base, 1n+g, h1)), z => hz => hr => shs.sound(1n+g, t, z, 1n+Nat.add(base, Shape.sp_ncaps(i)), r, hz, hr), z => hz => wt => shs.cap(g, i, t, s, base, r, z, hz, x => hx => shs.sound(1n+g, i, s, 1n+base, x, hf, hx), wt))
            case S.Opt{+i}:
              +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g, i, [s], base), [s]) : List<&2, S.St>}
              +b1 = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Opt{i} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.fits_app(1n+g, Shape.sp_reads(1n+g, i, [s], base), [s], LU.shu.pf(1n+g, i, [s], base, 1n+g, h1), h1), z => hz => hr => shs.sound(1n+g, t, z, Nat.add(base, Shape.sp_ncaps(i)), r, hz, hr), z => hz => wt => shs.opt(g, i, t, s, base, r, z, hz, x => hx => shs.sound(1n+g, i, s, base, x, hf, hx), wt))
            case S.Alt{+a, +bb}:
              +r1 = {List.append(&2, S.St, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)))) : List<&2, S.St>}
              +b1 = {Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)) : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Alt{a, bb} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.fits_app(1n+g, Shape.sp_reads(1n+g, a, [s], base), Shape.sp_reads(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a))), LU.shu.pf(1n+g, a, [s], base, 1n+g, h1), LU.shu.pf(1n+g, bb, [s], Nat.add(base, Shape.sp_ncaps(a)), 1n+g, h1)), z => hz => hr => shs.sound(1n+g, t, z, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), r, hz, hr), z => hz => wt => shs.alt(g, a, bb, t, s, base, r, z, hz, x => hx => shs.sound(1n+g, a, s, base, x, hf, hx), x => hx => shs.sound(1n+g, bb, s, Nat.add(base, Shape.sp_ncaps(a)), x, hf, hx), wt))
            case S.Many{+i, +min}:
              +r1 = {List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s)) : List<&2, S.St>}
              +b1 = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Many{i, min} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.fits_app(1n+g, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base), Shape.sp_zero(min, s), LU.shu.pf(g, [S.Many{i, Shape.sp_dec(min)}], Shape.sp_moved(Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base)), base, 1n+g, LU.shu.moved(1n+g, Shape.sp_left(s), Shape.sp_reads(1n+g, i, [s], base), LU.shu.pf(1n+g, i, [s], base, 1n+g, h1))), LU.shu.zero(min, 1n+g, s, hf)), z => hz => hr => shs.sound(1n+g, t, z, Nat.add(base, Shape.sp_ncaps(i)), r, hz, hr), z => hz => wt => shs.many(g, i, min, t, s, base, r, hf, z, hz, x => hx => shs.sound(1n+g, i, s, base, x, hf, hx), y => hy => hzm => shs.sound(g, [S.Many{i, Shape.sp_dec(min)}], y, base, z, hy, hzm), wt))
            case S.Ahead{+i, +neg}:
              +r1 = {Shape.sp_ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s) : List<&2, S.St>}
              +b1 = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Ahead{i, neg} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.ahead(neg, Shape.sp_reads(1n+g, i, [s], base), s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, Nat.add(base, Shape.sp_ncaps(i)), r, hz, hr), z => hz => wt => shs.ahead(neg, g, i, t, s, base, r, hf, z, hz, x => hx => shs.sound(1n+g, i, s, base, x, hf, hx), wt))
            case S.Same{+k}:
              +r1 = {Shape.sp_same(k, s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Same{k} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.same(k, s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.same(k, t, s, base, r, z, hz, wt))
            case S.Bound{}:
              +r1 = {Shape.sp_bound(s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Bound{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.bound(s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.bound(t, s, base, r, z, hz, wt))
            case S.Begin{}:
              +r1 = {Shape.sp_begin(s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.Begin{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.begin(s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.begin(t, s, base, r, z, hz, wt))
            case S.End{}:
              +r1 = {Shape.sp_end(s) : List<&2, S.St>}
              +b1 = {base : Nat}
              +h1 = {LU.shu.one(1n+g, s, hf) : {LU.shu.fits(1n+g, [s]) == True{} : Bool}}
              shs.go(&ws: List<&2, Shape.Part> -> {Shape.sp_split(ws, S.End{} <> t, base, Some{s}) == Some{r} : Maybe<&2, S.St>}, r1, g, t, b1, r, LH.shh.reads_from(1n+g, t, r1, r, b1, LR.shr.app_nil(r, Shape.sp_reads(1n+g, t, r1, b1), h)), LU.shu.end(s, 1n+g, hf), z => hz => hr => shs.sound(1n+g, t, z, base, r, hz, hr), z => hz => wt => shs.end(t, s, base, r, z, hz, wt))

