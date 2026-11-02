# eukhe: the laws of area shape: searches

import Base
import ../../bend/shape.bend as S
import ./match.bend as ShapeMatch

# (S2) Searches of a shape and of a list of shapes
# -----------------------------------------------
# bend/shape.bend `find`, `first`, `all` over the readings of
# laws/shape/match.bend (R1-R6 there). Every fuel, place, shape, list of
# shapes and text is free.
#
# R7: a search from a place answers the first place from it on (only that
#     place for AtStart) where the shape's pieces have an answer (R5, the
#     shape's ends), every place with no capture taken: that answer and
#     the count of chars before the place.
# R8: first over a list of shapes and a text answers the first shape with
#     a search answer from the text start (fuel one past the text's
#     length): its index from 0 and its fit: the char counts where it
#     starts and ends and the text each capture took (None: untaken).
# R9: all of a shape over a text answers its fits left to right, place by
#     place from the text start: a place is tried when no earlier fit
#     covers it (a fit from char p to char q covers the places after p up
#     to before q; an empty fit covers none) and the shape may start there
#     (AtStart: only the text start); its answer (R5, captures untaken,
#     fuel one past the text's length) is a fit. So each search starts
#     where the previous fit ended, one char later after an empty fit.
# R10: a fuel past a place's count of chars after it reads the place's
#     readings (law shape_fuel_enough), so the fuel of R8 and R9 reads
#     every reading of every place of the text.

# Spec helpers: searches
# ----------------------

def sp_try(m: Maybe<&2, S.St>, +p: Nat, more: Unit -> Maybe<&2, S.Hit>) -> Maybe<&2, S.Hit>:
  match m:
    case None{}:
      more(Unit{})
    case Some{r}:
      Some{S.Hit{r, p}}

def sp_next(st: S.Start, more: Unit -> Maybe<&2, S.Hit>) -> Maybe<&2, S.Hit>:
  match st:
    case S.AtStart{}:
      None{}
    case S.Anywhere{}:
      more(Unit{})

# R7: from the place (pos chars before it, left after it, word: the char
# before it is a word char, the text from it on, the captures caps) on,
# the first place with an answer, and that answer (AtStart: only the
# first place)
def sp_find.go(text: String, +f: Nat, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>) -> Maybe<&2, S.Hit>:
  match text:
    case SNil{}:
      sp_try(ShapeMatch.sp_answer(f, ps, ends, S.St{pos, left, word, SNil{}, caps}), pos, k => None{})
    case SCon{+x, +t}:
      sp_try(ShapeMatch.sp_answer(f, ps, ends, S.St{pos, left, word, SCon{x, t}, caps}), pos, k => sp_next(st, j => sp_find.go(t, f, st, ps, ends, 1n+pos, ShapeMatch.sp_dec(left), ShapeMatch.sp_word(x), caps)))

# R7: as many captures as the pieces hold, none taken
def sp_none_caps(n: Nat) -> List<&2, Maybe<&2, S.Got>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      None{} <> sp_none_caps(m)

# R7: the leftmost answer of the shape from the place a on, every place
# with no capture taken
def sp_find(f: Nat, sh: S.Shape, a: S.At) -> Maybe<&2, S.Hit>:
  match sh:
    case S.Shape{st, +ps, ends}:
      match a:
        case S.At{text, pos, left, word}:
          sp_find.go(text, f, st, ps, ends, pos, left, word, sp_none_caps(ShapeMatch.sp_ncaps(ps)))

# R8: the text a capture took
def sp_got_text(g: Maybe<&2, S.Got>) -> Maybe<&2, String>:
  match g:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case S.Got{at, to, from}:
          Some{String.take(from, Nat.sub(to, at))}

def sp_got_texts(cs: List<&2, Maybe<&2, S.Got>>) -> List<&2, Maybe<&2, String>>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      sp_got_text(c) <> sp_got_texts(t)

# R8: the fit of an answer r at a place with p chars before it: from char p
# to r's, the text of each capture
def sp_fit(p: Nat, r: S.St) -> S.Fit:
  match r:
    case S.St{pos, left, word, rest, caps}:
      S.Fit{p, pos, sp_got_texts(caps)}

# R8: the start of a text: no char before it, every char after it
def sp_start(+text: String) -> S.At:
  S.At{text, 0n, String.length(text), False{}}

def sp_first.hit(m: Maybe<&2, S.Hit>, +i: Nat, more: Unit -> Maybe<&2, S.Found>) -> Maybe<&2, S.Found>:
  match m:
    case None{}:
      more(Unit{})
    case Some{h}:
      match h:
        case S.Hit{r, p}:
          Some{S.Found{i, sp_fit(p, r)}}

def sp_first.go(shs: List<&2, S.Shape>, +f: Nat, +a: S.At, +i: Nat) -> Maybe<&2, S.Found>:
  match shs:
    case Nil{}:
      None{}
    case sh <> t:
      sp_first.hit(sp_find(f, sh, a), i, k => sp_first.go(t, f, a, 1n+i))

# R8: the first shape of the list with an answer from the text's start,
# its index (from 0) and its fit; fuel one past the text's length
def sp_first(shs: List<&2, S.Shape>, +text: String) -> Maybe<&2, S.Found>:
  sp_first.go(shs, 1n+String.length(text), sp_start(text), 0n)

# R9: whether a shape may start at a place with pos chars before it
def sp_may(st: S.Start, +pos: Nat) -> Bool:
  match st:
    case S.AtStart{}:
      Nat.is_eq(pos, 0n)
    case S.Anywhere{}:
      True{}

# R9: a place is tried when no earlier fit covers it and the shape may
# start there; its answer then, else none
def sp_tried(b: Bool, +f: Nat, +ps: List<&2, S.Piece>, +ends: Bool, s: S.St) -> Maybe<&2, S.St>:
  match b:
    case True{}:
      ShapeMatch.sp_answer(f, ps, ends, s)
    case False{}:
      None{}

# R9: how many places after the next one the fit from char p to r covers
def sp_covers(+p: Nat, r: S.St) -> Nat:
  match r:
    case S.St{pos, left, word, rest, caps}:
      ShapeMatch.sp_dec(Nat.sub(pos, p))

def sp_all.last(m: Maybe<&2, S.St>, +p: Nat) -> List<&2, S.Fit>:
  match m:
    case None{}:
      Nil{}
    case Some{r}:
      [sp_fit(p, r)]

def sp_all.step(m: Maybe<&2, S.St>, +p: Nat, cover: Nat, more: Nat -> List<&2, S.Fit>) -> List<&2, S.Fit>:
  match m:
    case None{}:
      more(ShapeMatch.sp_dec(cover))
    case Some{+r}:
      sp_fit(p, r) <> more(sp_covers(p, r))

# R9: the fits from a place (pos chars before it, left after it, word: the
# char before it is a word char, the text from it on, the captures caps)
# on, place by place; cover: how many places from here an earlier fit
# still covers
def sp_all.go(text: String, +f: Nat, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, +cover: Nat) -> List<&2, S.Fit>:
  match text:
    case SNil{}:
      sp_all.last(sp_tried(Bool.and(Nat.is_eq(cover, 0n), sp_may(st, pos)), f, ps, ends, S.St{pos, left, word, SNil{}, caps}), pos)
    case SCon{+x, +t}:
      sp_all.step(sp_tried(Bool.and(Nat.is_eq(cover, 0n), sp_may(st, pos)), f, ps, ends, S.St{pos, left, word, SCon{x, t}, caps}), pos, cover, k => sp_all.go(t, f, st, ps, ends, 1n+pos, ShapeMatch.sp_dec(left), ShapeMatch.sp_word(x), caps, k))

# R9: every fit of the shape in the text, left to right (fuel one past the
# text's length, captures untaken at each place)
def sp_all(sh: S.Shape, +text: String) -> List<&2, S.Fit>:
  match sh:
    case S.Shape{st, +ps, ends}:
      sp_all.go(text, 1n+String.length(text), st, ps, ends, 0n, String.length(text), False{}, sp_none_caps(ShapeMatch.sp_ncaps(ps)), 0n)

# LAW shape_find (R7): from every place, for every fuel and shape, the
# search answers the first place (only the first for AtStart) where the
# shape has an answer, every place with all captures untaken
# EXCLUDES: a place skipped, a later place preferred, an anywhere shape
#   searched only at the start or an AtStart one past it, captures carried
#   from a failed place, a place's word char or counts off by one
law shape_find:
  for +f: Nat
  for +sh: S.Shape
  for +a: S.At
  {S.find(f, sh, a) == sp_find(f, sh, a) : Maybe<&2, S.Hit>}

# LAW shape_first_of (R8): for every list of shapes and text, the first
# shape with a fit, its index and its fit (span and the text of each
# capture, None for an untaken one)
# EXCLUDES: a later shape preferred to an earlier one that fits, an index
#   off by one, a span or a capture text cut wrong, an untaken capture read
#   as empty
law shape_first_of:
  for +shs: List<&2, S.Shape>
  for +text: String
  {S.first(shs, text) == sp_first(shs, text) : Maybe<&2, S.Found>}

# LAW shape_all (R9): for every shape and text, the fits left to right,
# each the leftmost from where the previous one ended (one char later
# after an empty fit)
# EXCLUDES: overlapping fits, a fit skipped, an empty fit repeated forever
#   or dropped, a search that restarts at the text start
law shape_all:
  for +sh: S.Shape
  for +text: String
  {S.all(sh, text) == sp_all(sh, text) : List<&2, S.Fit>}

# Examples
# --------

# R1: no White_Space (regex `\S`)
def ex_nws() -> S.Cls:
  S.Cls{S.Space{}, True{}, False{}}

# R1: a-z (regex `[a-z]`)
def ex_az() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{97, 122}]}, False{}, False{}}

def ex_at(ps: List<&2, S.Piece>, ends: Bool) -> S.Shape:
  S.Shape{S.AtStart{}, ps, ends}

def ex_any(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, False{}}

def ex_fit(at: Nat, to: Nat, caps: List<&2, Maybe<&2, String>>) -> Maybe<&2, S.Found>:
  Some{S.Found{0n, S.Fit{at, to, caps}}}

# LAW shape_example (R1-R9): anchor: `^R (\S+)$` fits "R w1" and not
# "R w1 x"; `(\S+)1` gives the run back to "ab1c"; `a(b)?c` on "ac" leaves
# its capture untaken; `(a|ab)c` on "abc" takes the second option after the
# first fails later; `(ab)+` keeps the last round; `(a)\1` reads its
# capture again; `\bb` skips the b inside a word; `a(?!b)` skips the a
# before b; Fold "ab" fits "AB"; `[a-z]` fits a later shape of a list
# EXCLUDES: a matcher that drifts from the regex engine it replaced
law shape_example:
  {[S.first([ex_at([S.Lit{"R "}, S.Cap{[S.Run{ex_nws(), 1n, None{}}]}], True{})], "R w1"), S.first([ex_at([S.Lit{"R "}, S.Cap{[S.Run{ex_nws(), 1n, None{}}]}], True{})], "R w1 x"), S.first([ex_any([S.Cap{[S.Run{ex_nws(), 1n, None{}}]}, S.Lit{"1"}])], "ab1c1"), S.first([ex_any([S.Lit{"a"}, S.Opt{[S.Cap{[S.Lit{"b"}]}]}, S.Lit{"c"}])], "ac"), S.first([ex_any([S.Cap{[S.Alt{[S.Lit{"a"}], [S.Lit{"ab"}]}]}, S.Lit{"c"}])], "abc"), S.first([ex_any([S.Many{[S.Cap{[S.Lit{"ab"}]}], 1n}])], "ababx"), S.first([ex_any([S.Cap{[S.Lit{"a"}]}, S.Same{1n}])], "xaa"), S.first([ex_any([S.Bound{}, S.Lit{"b"}])], "ab b"), S.first([ex_any([S.Lit{"a"}, S.Ahead{[S.Lit{"b"}], True{}}])], "aba"), S.first([ex_any([S.Fold{"ab"}])], "xAB"), S.first([ex_at([S.Lit{"x"}], False{}), ex_any([S.Run{ex_az(), 1n, Some{1n}}])], "1q")] == [ex_fit(0n, 4n, [Some{"w1"}]), None{}, ex_fit(0n, 5n, [Some{"ab1c"}]), ex_fit(0n, 2n, [None{}]), ex_fit(0n, 3n, [Some{"ab"}]), ex_fit(0n, 4n, [Some{"ab"}]), ex_fit(1n, 3n, [Some{"a"}]), ex_fit(3n, 4n, []), ex_fit(2n, 3n, []), ex_fit(1n, 3n, []), Some{S.Found{1n, S.Fit{1n, 2n, []}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW shape_all_example (R9): anchor: `[a-z]*` on "ba1" fits "ba" and then
# the empty text before and after the 1; `(a)` on "aa" fits twice
# EXCLUDES: an empty fit repeated or dropped, a search that does not go on
#   where the previous fit ended, an AtStart shape fitted past the start
law shape_all_example:
  {(S.all(ex_any([S.Run{ex_az(), 0n, None{}}]), "ba1"), S.all(ex_any([S.Cap{[S.Lit{"a"}]}]), "aa"), S.all(ex_at([S.Lit{"a"}], False{}), "aa")) == ([S.Fit{0n, 2n, []}, S.Fit{2n, 2n, []}, S.Fit{3n, 3n, []}], [S.Fit{0n, 1n, [Some{"a"}]}, S.Fit{1n, 2n, [Some{"a"}]}], [S.Fit{0n, 1n, []}]) : List<&2, S.Fit> & (List<&2, S.Fit> & List<&2, S.Fit>)}

# LAW shape_fuel_enough (R10): any fuel past a place's count of chars after
# it reads exactly the place's readings
# EXCLUDES: a search whose fuel cuts a repetition short, or reads rounds a
#   place does not have
law shape_fuel_enough:
  for +f: Nat
  for +ps: List<&2, S.Piece>
  for +s: S.St
  for h: {Nat.is_lt(ShapeMatch.sp_left(s), f) == True{} : Bool}
  {ShapeMatch.sp_reads(f, ps, [s], 0n) == ShapeMatch.sp_readings(ps, s) : List<&2, S.St>}
