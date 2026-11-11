# eukhe: the matcher's searches are the spec's (laws/shape/search.bend R7-R9):
# the answer at each place is the spec's (the backtracking matcher,
# proof/shape/base/seek.bend), and the places, shapes and fits follow the
# spec's order, by induction along the code.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../../../laws/shape/search.bend as ShapeSearch
import ./leaf.bend as LL
import ./seek.bend as LK
import ./fuel.bend as LU
import ./sound.bend as LS
import ../shape_first_reading.bend as LFR

def shf2.caps(n: Nat) -> {S.none_caps(n) == ShapeSearch.sp_none_caps(n) : List<&2, Maybe<&2, S.Got>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(List<&2, Maybe<&2, S.Got>>, List<&2, Maybe<&2, S.Got>>, r => None{} <> r, S.none_caps(m), ShapeSearch.sp_none_caps(m), shf2.caps(m))

def shf2.try(m: Maybe<&2, S.St>, +p: Nat, -X: Maybe<&2, S.Hit>, -Y: Maybe<&2, S.Hit>, h: {X == Y : Maybe<&2, S.Hit>}) -> {S.find.try(m, p, k => X) == ShapeSearch.sp_try(m, p, k => Y) : Maybe<&2, S.Hit>}:
  match m:
    case None{}:
      h
    case Some{r}:
      {==}

def shf2.next(st: S.Start, -X: Maybe<&2, S.Hit>, -Y: Maybe<&2, S.Hit>, h: {X == Y : Maybe<&2, S.Hit>}) -> {S.find.next(st, k => X) == ShapeSearch.sp_next(st, k => Y) : Maybe<&2, S.Hit>}:
  match st:
    case S.AtStart{}:
      {==}
    case S.Anywhere{}:
      h

# Fits
# ----

def shf2.got(g: Maybe<&2, S.Got>) -> {S.got_text(g) == ShapeSearch.sp_got_text(g) : Maybe<&2, String>}:
  match g:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case S.Got{at, to, from}:
          {==}

def shf2.texts(cs: List<&2, Maybe<&2, S.Got>>) -> {S.texts(cs) == ShapeSearch.sp_got_texts(cs) : List<&2, Maybe<&2, String>>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(Maybe<&2, String>, S.got_text(c), ShapeSearch.sp_got_text(c), shf2.got(c)) : {_ <> S.texts(t) == ShapeSearch.sp_got_texts(c <> t) : List<&2, Maybe<&2, String>>}
      Equal.cong(List<&2, Maybe<&2, String>>, List<&2, Maybe<&2, String>>, r => ShapeSearch.sp_got_text(c) <> r, S.texts(t), ShapeSearch.sp_got_texts(t), shf2.texts(t))

def shf2.fit(+p: Nat, r: S.St) -> {S.fit(p, r) == ShapeSearch.sp_fit(p, r) : S.Fit}:
  match r:
    case S.St{+pos, left, word, rest, +caps}:
      Equal.cong(List<&2, Maybe<&2, String>>, S.Fit, xs => S.Fit{p, pos, xs}, S.texts(caps), ShapeSearch.sp_got_texts(caps), shf2.texts(caps))

def shf2.hit(m: Maybe<&2, S.Hit>, +i: Nat, -X: Maybe<&2, S.Found>, -Y: Maybe<&2, S.Found>, h: {X == Y : Maybe<&2, S.Found>}) -> {S.first.hit(m, i, k => X) == ShapeSearch.sp_first.hit(m, i, k => Y) : Maybe<&2, S.Found>}:
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case S.Hit{+r, +p}:
          Equal.cong(S.Fit, Maybe<&2, S.Found>, w => Some{S.Found{i, w}}, S.fit(p, r), ShapeSearch.sp_fit(p, r), shf2.fit(p, r))

# the matcher's answer at a place is the spec's, any fuel past its count
def shf2.fast_at(+f: Nat, +ps: List<&2, S.Piece>, +ends: Bool, +s: S.St, h: {Nat.is_lt(Shape.sp_left(s), f) == True{} : Bool}) -> {S.first_at(ps, ends, s) == Shape.sp_answer(f, ps, ends, s) : Maybe<&2, S.St>}:
  LK.shk.seek(S.budget(s), S.Want{s}, f, ps, S.BAt{0n}, S.FEnd{}, ends, LU.shu.one(f, s, h))

# `first`'s search is the spec's, each place's answer by the matcher
def shf2.ffind(text: String, +f: Nat, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, +h: {Nat.is_lt(left, f) == True{} : Bool}) -> {S.first.find(text, st, ps, ends, pos, left, word, caps) == ShapeSearch.sp_find.go(text, f, st, ps, ends, pos, left, word, caps) : Maybe<&2, S.Hit>}:
  match text:
    case SNil{}:
      +s = {S.St{pos, left, word, SNil{}, caps} : S.St}
      %Equal.sym(Maybe<&2, S.St>, S.first_at(ps, ends, s), Shape.sp_answer(f, ps, ends, s), shf2.fast_at(f, ps, ends, s, h)) : {S.find.try(_, pos, k => None{}) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => None{}) : Maybe<&2, S.Hit>}
      shf2.try(Shape.sp_answer(f, ps, ends, s), pos, None{}, None{}, {==})
    case SCon{+x, +t}:
      +s = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
      +A = {S.find.next(st, j => S.first.find(t, st, ps, ends, 1n+pos, S.pred(left), S.is_word(x), caps)) : Maybe<&2, S.Hit>}
      +B = {ShapeSearch.sp_next(st, j => ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps)) : Maybe<&2, S.Hit>}
      %Equal.sym(Maybe<&2, S.St>, S.first_at(ps, ends, s), Shape.sp_answer(f, ps, ends, s), shf2.fast_at(f, ps, ends, s, h)) : {S.find.try(_, pos, k => A) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), LL.shl.pred(left)) : {S.find.try(Shape.sp_answer(f, ps, ends, s), pos, k => S.find.next(st, j => S.first.find(t, st, ps, ends, 1n+pos, _, S.is_word(x), caps))) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), LL.shl.word(x)) : {S.find.try(Shape.sp_answer(f, ps, ends, s), pos, k => S.find.next(st, j => S.first.find(t, st, ps, ends, 1n+pos, Shape.sp_dec(left), _, caps))) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      +C = {S.first.find(t, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : Maybe<&2, S.Hit>}
      +D = {ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : Maybe<&2, S.Hit>}
      shf2.try(Shape.sp_answer(f, ps, ends, s), pos, S.find.next(st, j => C), B, shf2.next(st, C, D, shf2.ffind(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, LU.shu.lt_dec(left, f, h))))

# a shape's search from the text start is the spec's
def shf2.fshape(sh: S.Shape, +text: String) -> {S.first.shape(sh, text, String.length(text)) == ShapeSearch.sp_find(1n+String.length(text), sh, ShapeSearch.sp_start(text)) : Maybe<&2, S.Hit>}:
  match sh:
    case S.Shape{+st, +ps, +ends}:
      +n = {String.length(text) : Nat}
      %Equal.sym(Nat, S.ncaps(ps), Shape.sp_ncaps(ps), LL.shl.ncaps(ps)) : {S.first.find(text, st, ps, ends, 0n, n, False{}, S.none_caps(_)) == ShapeSearch.sp_find(1n+n, S.Shape{st, ps, ends}, ShapeSearch.sp_start(text)) : Maybe<&2, S.Hit>}
      %Equal.sym(List<&2, Maybe<&2, S.Got>>, S.none_caps(Shape.sp_ncaps(ps)), ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)), shf2.caps(Shape.sp_ncaps(ps))) : {S.first.find(text, st, ps, ends, 0n, n, False{}, _) == ShapeSearch.sp_find(1n+n, S.Shape{st, ps, ends}, ShapeSearch.sp_start(text)) : Maybe<&2, S.Hit>}
      shf2.ffind(text, 1n+n, st, ps, ends, 0n, n, False{}, ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)), LS.shs.lt_self(n))

def shf2.first(shs: List<&2, S.Shape>, +text: String, +i: Nat) -> {S.first.go(shs, text, String.length(text), i) == ShapeSearch.sp_first.go(shs, 1n+String.length(text), ShapeSearch.sp_start(text), i) : Maybe<&2, S.Found>}:
  match shs:
    case Nil{}:
      {==}
    case +sh <> +t:
      +f = {1n+String.length(text) : Nat}
      +a = {ShapeSearch.sp_start(text) : S.At}
      %Equal.sym(Maybe<&2, S.Hit>, S.first.shape(sh, text, String.length(text)), ShapeSearch.sp_find(f, sh, a), shf2.fshape(sh, text)) : {S.first.hit(_, i, k => S.first.go(t, text, String.length(text), 1n+i)) == ShapeSearch.sp_first.go(sh <> t, f, a, i) : Maybe<&2, S.Found>}
      shf2.hit(ShapeSearch.sp_find(f, sh, a), i, S.first.go(t, text, String.length(text), 1n+i), ShapeSearch.sp_first.go(t, f, a, 1n+i), shf2.first(t, text, 1n+i))

# All
# ---

def shf2.may(st: S.Start, +pos: Nat) -> {S.may(st, pos) == ShapeSearch.sp_may(st, pos) : Bool}:
  match st:
    case S.AtStart{}:
      {==}
    case S.Anywhere{}:
      {==}

def shf2.tried(b: Bool, +f: Nat, +ps: List<&2, S.Piece>, +ends: Bool, +s: S.St, h: {Nat.is_lt(Shape.sp_left(s), f) == True{} : Bool}) -> {S.all.try(b, ps, ends, s) == ShapeSearch.sp_tried(b, f, ps, ends, s) : Maybe<&2, S.St>}:
  match b:
    case True{}:
      shf2.fast_at(f, ps, ends, s, h)
    case False{}:
      {==}

def shf2.skip(+p: Nat, r: S.St) -> {S.all.skip(p, r) == ShapeSearch.sp_covers(p, r) : Nat}:
  match r:
    case S.St{+pos, left, word, rest, caps}:
      LL.shl.pred(Nat.sub(pos, p))

def shf2.end(m: Maybe<&2, S.St>, +p: Nat) -> {S.all.end(m, p) == ShapeSearch.sp_all.last(m, p) : List<&2, S.Fit>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      Equal.cong(S.Fit, List<&2, S.Fit>, w => [w], S.fit(p, r), ShapeSearch.sp_fit(p, r), shf2.fit(p, r))

def shf2.here(m: Maybe<&2, S.St>, +p: Nat, +skip: Nat, -m1: Nat -> List<&2, S.Fit>, -m2: Nat -> List<&2, S.Fit>, h: @k: Nat -> {m1(k) == m2(k) : List<&2, S.Fit>}) -> {S.all.here(m, p, skip, m1) == ShapeSearch.sp_all.step(m, p, skip, m2) : List<&2, S.Fit>}:
  match m:
    case None{}:
      %Equal.sym(Nat, S.pred(skip), Shape.sp_dec(skip), LL.shl.pred(skip)) : {m1(_) == m2(Shape.sp_dec(skip)) : List<&2, S.Fit>}
      h(Shape.sp_dec(skip))
    case Some{+r}:
      %Equal.sym(S.Fit, S.fit(p, r), ShapeSearch.sp_fit(p, r), shf2.fit(p, r)) : {_ <> m1(S.all.skip(p, r)) == ShapeSearch.sp_fit(p, r) <> m2(ShapeSearch.sp_covers(p, r)) : List<&2, S.Fit>}
      %Equal.sym(Nat, S.all.skip(p, r), ShapeSearch.sp_covers(p, r), shf2.skip(p, r)) : {ShapeSearch.sp_fit(p, r) <> m1(_) == ShapeSearch.sp_fit(p, r) <> m2(ShapeSearch.sp_covers(p, r)) : List<&2, S.Fit>}
      Equal.cong(List<&2, S.Fit>, List<&2, S.Fit>, xs => ShapeSearch.sp_fit(p, r) <> xs, m1(ShapeSearch.sp_covers(p, r)), m2(ShapeSearch.sp_covers(p, r)), h(ShapeSearch.sp_covers(p, r)))

def shf2.allgo(text: String, +f: Nat, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, +skip: Nat, +h: {Nat.is_lt(left, f) == True{} : Bool}) -> {S.all.go(text, st, ps, ends, pos, left, word, caps, skip) == ShapeSearch.sp_all.go(text, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}:
  match text:
    case SNil{}:
      +s = {S.St{pos, left, word, SNil{}, caps} : S.St}
      %Equal.sym(Bool, S.may(st, pos), ShapeSearch.sp_may(st, pos), shf2.may(st, pos)) : {S.all.end(S.all.try(Bool.and(Nat.is_eq(skip, 0n), _), ps, ends, s), pos) == ShapeSearch.sp_all.go(SNil{}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      +b = {Bool.and(Nat.is_eq(skip, 0n), ShapeSearch.sp_may(st, pos)) : Bool}
      %Equal.sym(Maybe<&2, S.St>, S.all.try(b, ps, ends, s), ShapeSearch.sp_tried(b, f, ps, ends, s), shf2.tried(b, f, ps, ends, s, h)) : {S.all.end(_, pos) == ShapeSearch.sp_all.go(SNil{}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      shf2.end(ShapeSearch.sp_tried(b, f, ps, ends, s), pos)
    case SCon{+x, +t}:
      +s = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
      %Equal.sym(Bool, S.may(st, pos), ShapeSearch.sp_may(st, pos), shf2.may(st, pos)) : {S.all.here(S.all.try(Bool.and(Nat.is_eq(skip, 0n), _), ps, ends, s), pos, skip, k => S.all.go(t, st, ps, ends, 1n+pos, S.pred(left), S.is_word(x), caps, k)) == ShapeSearch.sp_all.go(SCon{x, t}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      +b = {Bool.and(Nat.is_eq(skip, 0n), ShapeSearch.sp_may(st, pos)) : Bool}
      %Equal.sym(Maybe<&2, S.St>, S.all.try(b, ps, ends, s), ShapeSearch.sp_tried(b, f, ps, ends, s), shf2.tried(b, f, ps, ends, s, h)) : {S.all.here(_, pos, skip, k => S.all.go(t, st, ps, ends, 1n+pos, S.pred(left), S.is_word(x), caps, k)) == ShapeSearch.sp_all.go(SCon{x, t}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), LL.shl.pred(left)) : {S.all.here(ShapeSearch.sp_tried(b, f, ps, ends, s), pos, skip, k => S.all.go(t, st, ps, ends, 1n+pos, _, S.is_word(x), caps, k)) == ShapeSearch.sp_all.go(SCon{x, t}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), LL.shl.word(x)) : {S.all.here(ShapeSearch.sp_tried(b, f, ps, ends, s), pos, skip, k => S.all.go(t, st, ps, ends, 1n+pos, Shape.sp_dec(left), _, caps, k)) == ShapeSearch.sp_all.go(SCon{x, t}, f, st, ps, ends, pos, left, word, caps, skip) : List<&2, S.Fit>}
      +hl = {LU.shu.lt_dec(left, f, h) : {Nat.is_lt(Shape.sp_dec(left), f) == True{} : Bool}}
      shf2.here(ShapeSearch.sp_tried(b, f, ps, ends, s), pos, skip, k => S.all.go(t, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, k), k => ShapeSearch.sp_all.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, k), k => shf2.allgo(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, k, hl))

# all of a shape is the spec's
def shf2.all(sh: S.Shape, +text: String) -> {S.all(sh, text) == ShapeSearch.sp_all(sh, text) : List<&2, S.Fit>}:
  match sh:
    case S.Shape{+st, +ps, +ends}:
      +n = {String.length(text) : Nat}
      %Equal.sym(Nat, S.ncaps(ps), Shape.sp_ncaps(ps), LL.shl.ncaps(ps)) : {S.all.go(text, st, ps, ends, 0n, n, False{}, S.none_caps(_), 0n) == ShapeSearch.sp_all(S.Shape{st, ps, ends}, text) : List<&2, S.Fit>}
      %Equal.sym(List<&2, Maybe<&2, S.Got>>, S.none_caps(Shape.sp_ncaps(ps)), ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)), shf2.caps(Shape.sp_ncaps(ps))) : {S.all.go(text, st, ps, ends, 0n, n, False{}, _, 0n) == ShapeSearch.sp_all(S.Shape{st, ps, ends}, text) : List<&2, S.Fit>}
      shf2.allgo(text, 1n+n, st, ps, ends, 0n, n, False{}, ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)), 0n, LS.shs.lt_self(n))

def shf2.at(+f: Nat, +ps: List<&2, S.Piece>, +ends: Bool, +s: S.St) -> {S.at(f, ps, ends, s) == Shape.sp_answer(f, ps, ends, s) : Maybe<&2, S.St>}:
  Shape.shape_first_reading(f, ps, ends, s)

def shf2.go(text: String, +f: Nat, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>) -> {S.find.go(text, f, st, ps, ends, pos, left, word, caps) == ShapeSearch.sp_find.go(text, f, st, ps, ends, pos, left, word, caps) : Maybe<&2, S.Hit>}:
  match text:
    case SNil{}:
      +s = {S.St{pos, left, word, SNil{}, caps} : S.St}
      %Equal.sym(Maybe<&2, S.St>, S.at(f, ps, ends, s), Shape.sp_answer(f, ps, ends, s), shf2.at(f, ps, ends, s)) : {S.find.try(_, pos, k => None{}) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => None{}) : Maybe<&2, S.Hit>}
      shf2.try(Shape.sp_answer(f, ps, ends, s), pos, None{}, None{}, {==})
    case SCon{+x, +t}:
      +s = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
      +A = {S.find.next(st, j => S.find.go(t, f, st, ps, ends, 1n+pos, S.pred(left), S.is_word(x), caps)) : Maybe<&2, S.Hit>}
      +B = {ShapeSearch.sp_next(st, j => ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps)) : Maybe<&2, S.Hit>}
      %Equal.sym(Maybe<&2, S.St>, S.at(f, ps, ends, s), Shape.sp_answer(f, ps, ends, s), shf2.at(f, ps, ends, s)) : {S.find.try(_, pos, k => A) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), LL.shl.pred(left)) : {S.find.try(Shape.sp_answer(f, ps, ends, s), pos, k => S.find.next(st, j => S.find.go(t, f, st, ps, ends, 1n+pos, _, S.is_word(x), caps))) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), LL.shl.word(x)) : {S.find.try(Shape.sp_answer(f, ps, ends, s), pos, k => S.find.next(st, j => S.find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), _, caps))) == ShapeSearch.sp_try(Shape.sp_answer(f, ps, ends, s), pos, k => B) : Maybe<&2, S.Hit>}
      +C = {S.find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : Maybe<&2, S.Hit>}
      +D = {ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : Maybe<&2, S.Hit>}
      shf2.try(Shape.sp_answer(f, ps, ends, s), pos, S.find.next(st, j => C), B, shf2.next(st, C, D, shf2.go(t, f, st, ps, ends, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps)))

# the search of a shape is the spec's
def shf2.find(+f: Nat, sh: S.Shape, a: S.At) -> {S.find(f, sh, a) == ShapeSearch.sp_find(f, sh, a) : Maybe<&2, S.Hit>}:
  match sh:
    case S.Shape{+st, +ps, +ends}:
      match a:
        case S.At{+text, +pos, +left, +word}:
          %Equal.sym(Nat, S.ncaps(ps), Shape.sp_ncaps(ps), LL.shl.ncaps(ps)) : {S.find.go(text, f, st, ps, ends, pos, left, word, S.none_caps(_)) == ShapeSearch.sp_find(f, S.Shape{st, ps, ends}, S.At{text, pos, left, word}) : Maybe<&2, S.Hit>}
          %Equal.sym(List<&2, Maybe<&2, S.Got>>, S.none_caps(Shape.sp_ncaps(ps)), ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)), shf2.caps(Shape.sp_ncaps(ps))) : {S.find.go(text, f, st, ps, ends, pos, left, word, _) == ShapeSearch.sp_find(f, S.Shape{st, ps, ends}, S.At{text, pos, left, word}) : Maybe<&2, S.Hit>}
          shf2.go(text, f, st, ps, ends, pos, left, word, ShapeSearch.sp_none_caps(Shape.sp_ncaps(ps)))
