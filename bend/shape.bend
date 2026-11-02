# shape: explicit line shapes, the rule eukhe states instead of a regex in a
# decision (laws/shape.bend). A shape is data: where it may start (at the
# text start, or anywhere: the leftmost place it fits), a list of pieces,
# and whether it must end the text. The pieces read the text from the
# place in order; a piece that can read it in several ways tries them in
# a fixed order (a run longest first, an optional piece taken before
# skipped, options in their order, a repetition with more rounds first)
# and the first way that lets the rest fit wins, as a backtracking regex
# engine would (the searches run the matcher below; `at` computes every
# reading). The tables of shapes are data of the modules that use them
# (bend/incident_shapes.bend), written out whole so the compiled core
# holds them as constants; the entry names a shape by a global id
# (bend/ffi_shape.bend). A word char is an ASCII letter, an ASCII digit or
# `_`; a digit is an ASCII digit. Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as TP

# Classes, pieces, shapes
# -----------------------

# the char codes from lo to hi, both in
type Rg is Data:
  Rg{lo: U32, hi: U32}

# the chars a class names before its flags
type Chars is Data:
  # a char whose code is in one of the ranges
  Codes{rs: List<&2, Rg>}
  # a Unicode White_Space char (bend/text_pat.bend `is_ws`)
  Space{}

# a class of chars: the chars of the set (neg: every other char); fold: an
# ASCII letter is named when it or its other case is
type Cls is Data:
  Cls{set: Chars, neg: Bool, fold: Bool}

type Piece is Data:
  # exactly the text s
  Lit{s: String}
  # the text s with ASCII letters in either case (s written lowercase)
  Fold{s: String}
  # from min to max (None: no limit) chars of the class c, as many as the
  # rest still allows
  Run{c: Cls, min: Nat, max: Maybe<&2, Nat>}
  # the pieces ps, their text captured (captures are numbered from 1 in the
  # order their Cap opens, as regex groups)
  Cap{ps: List<&2, Piece>}
  # the pieces ps, or nothing (taking them tried first)
  Opt{ps: List<&2, Piece>}
  # the pieces a, or else the pieces b (a tried first; more options nest
  # in b: Alt{a, [Alt{b, c}]})
  Alt{a: List<&2, Piece>, b: List<&2, Piece>}
  # the pieces ps repeated, each round reading at least one char, at least
  # min times, as many rounds as the rest allows
  Many{ps: List<&2, Piece>, min: Nat}
  # no char: the pieces ps read a prefix of the text from here (neg: they
  # read none); captures inside are not kept
  Ahead{ps: List<&2, Piece>, neg: Bool}
  # exactly the text capture k took (k from 1; none taken: never fits)
  Same{k: Nat}
  # no char: a word boundary (the chars on its two sides, or the text edge,
  # differ in being a word char)
  Bound{}
  # no char: the text start
  Begin{}
  # no char: the text end
  End{}

type Start is Data:
  # only at the text start
  AtStart{}
  # at the leftmost place it fits
  Anywhere{}

type Shape is Data:
  Shape{start: Start, ps: List<&2, Piece>, ends: Bool}

# Places and readings
# -------------------

# a capture: from char at to char to; from: the text from at on
type Got is Data:
  Got{at: Nat, to: Nat, from: String}

# a place in the text and the captures read so far: pos chars before it,
# left chars after it, whether the char before it is a word char, the text
# from it on, one entry per capture
type St is Data:
  St{pos: Nat, left: Nat, word: Bool, rest: String, caps: List<&2, Maybe<&2, Got>>}

# how readings are asked for: every reading in order, or only the first
# whose end condition holds (ends: the text must end there)
type Mode is Data:
  All{}
  First{ends: Bool}

# a fit: the chars from at to to, and the text each capture took
type Fit is Data:
  Fit{at: Nat, to: Nat, caps: List<&2, Maybe<&2, String>>}

# a reading r of a shape that started at char at
type Hit is Data:
  Hit{r: St, at: Nat}

# the index i of the first shape of a list that fits, and its fit
type Found is Data:
  Found{i: Nat, fit: Fit}

# Chars
# -----

def in_range(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# whether x is in one of the ranges rs, or hit already holds (a tail
# loop: it stops at the first range that holds x)
def in_rgs.go(rs: List<&2, Rg>, hit: Bool, +x: U32) -> Bool:
  match rs:
    case Nil{}:
      hit
    case r <> t:
      match r:
        case Rg{lo, hi}:
          match hit:
            case True{}:
              True{}
            case False{}:
              in_rgs.go(t, in_range(x, lo, hi), x)

def in_rgs(rs: List<&2, Rg>, +x: U32) -> Bool:
  in_rgs.go(rs, False{}, x)

def in_set(st: Chars, +c: Char) -> Bool:
  match st:
    case Codes{rs}:
      in_rgs(rs, Char.to_u32(c))
    case Space{}:
      TP.is_ws(c)

def swap.at(+x: U32, up: Bool, low: Bool) -> Char:
  match up low:
    case True{} _:
      Chr{U32.add(x, 32)}
    case False{} True{}:
      Chr{U32.sub(x, 32)}
    case False{} False{}:
      Chr{x}

# the other case of an ASCII letter; any other char itself
def swap(c: Char) -> Char:
  match c:
    case Chr{+x}:
      swap.at(x, in_range(x, 65, 90), in_range(x, 97, 122))

def is_in.fold(fold: Bool, st: Chars, c: Char) -> Bool:
  match fold:
    case True{}:
      in_set(st, swap(c))
    case False{}:
      False{}

# whether the char c is of the class k
def is_in(k: Cls, +c: Char) -> Bool:
  match k:
    case Cls{+st, neg, fold}:
      Bool.xor(neg, Bool.or(in_set(st, c), is_in.fold(fold, st, c)))

# a word char: an ASCII letter, an ASCII digit or `_`
def is_word(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(in_range(x, 97, 122), Bool.or(in_range(x, 65, 90), Bool.or(in_range(x, 48, 57), U32.is_eq(x, 95))))

# an ASCII letter in lowercase; any other char itself
def low.at(+x: U32, up: Bool) -> Char:
  match up:
    case True{}:
      Chr{U32.add(x, 32)}
    case False{}:
      Chr{x}

def low(c: Char) -> Char:
  match c:
    case Chr{+x}:
      low.at(x, in_range(x, 65, 90))

# whether the text s starts with a word char
def next_word(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{x, t}:
      is_word(x)

# Leaves
# ------

# one less, never below 0
def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      m

def keep(b: Bool, s: St) -> Maybe<&2, St>:
  match b:
    case True{}:
      Some{s}
    case False{}:
      None{}

# the place, as a list of none or one place
def m2l(m: Maybe<&2, St>) -> List<&2, St>:
  match m:
    case None{}:
      Nil{}
    case Some{s}:
      [s]

def lit.same(fold: Bool, +x: Char, +y: Char) -> Bool:
  match fold:
    case True{}:
      Char.is_eq(low(x), low(y))
    case False{}:
      Char.is_eq(x, y)

# the place after the text u read exactly (Lit; Fold with fold: ASCII
# letters in either case), when ok: the chars read so far fit
def lit.go(u: String, +fold: Bool, ok: Bool, rest: String, +pos: Nat, +left: Nat, word: Bool, caps: List<&2, Maybe<&2, Got>>) -> Maybe<&2, St>:
  match u:
    case SNil{}:
      keep(ok, St{pos, left, word, rest, caps})
    case SCon{+y, v}:
      match ok:
        case True{}:
          match rest:
            case SNil{}:
              None{}
            case SCon{+x, t}:
              lit.go(v, fold, lit.same(fold, x, y), t, 1n+pos, pred(left), is_word(x), caps)
        case False{}:
          None{}

def lit(u: String, fold: Bool, s: St) -> Maybe<&2, St>:
  match s:
    case St{pos, left, word, rest, caps}:
      lit.go(u, fold, True{}, rest, pos, left, word, caps)

# the place after the first n chars of from (all of them when it has
# fewer), when the text goes on with them (ok: the chars read so far fit)
def same.go(n: Nat, from: String, ok: Bool, rest: String, +pos: Nat, +left: Nat, word: Bool, caps: List<&2, Maybe<&2, Got>>) -> Maybe<&2, St>:
  match n:
    case 0n:
      keep(ok, St{pos, left, word, rest, caps})
    case 1n+m:
      match from:
        case SNil{}:
          keep(ok, St{pos, left, word, rest, caps})
        case SCon{+y, f}:
          match ok:
            case True{}:
              match rest:
                case SNil{}:
                  None{}
                case SCon{+x, t}:
                  same.go(m, f, Char.is_eq(x, y), t, 1n+pos, pred(left), is_word(x), caps)
            case False{}:
              None{}

def same.got(g: Maybe<&2, Maybe<&2, Got>>, s: St) -> Maybe<&2, St>:
  match g:
    case None{}:
      None{}
    case Some{c}:
      match c:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Got{at, to, from}:
              match s:
                case St{pos, left, word, rest, caps}:
                  same.go(Nat.sub(to, at), from, True{}, rest, pos, left, word, caps)

# the place after the text capture k took (k from 1)
def same(k: Nat, s: St) -> Maybe<&2, St>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      match s:
        case St{pos, left, word, rest, +caps}:
          same.got(List.get(&2, Maybe<&2, Got>, caps, j), St{pos, left, word, rest, caps})

def run.push(need: Nat, s: St, acc: List<&2, St>) -> List<&2, St>:
  match need:
    case 0n:
      s <> acc
    case 1n+n:
      acc

def run.room(room: Maybe<&2, Nat>) -> Bool:
  match room:
    case None{}:
      True{}
    case Some{n}:
      match n:
        case 0n:
          False{}
        case 1n+m:
          True{}

def run.less(room: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match room:
    case None{}:
      None{}
    case Some{n}:
      match n:
        case 0n:
          Some{0n}
        case 1n+m:
          Some{m}

def or_else(b: Bool, k: Unit -> List<&2, St>, d: List<&2, St>) -> List<&2, St>:
  match b:
    case True{}:
      k(Unit{})
    case False{}:
      d

# the places after a run of chars of c from the text rest, the longest run
# first, before acc: need more chars must still come, room more may
def run.go(rest: String, +c: Cls, +need: Nat, +room: Maybe<&2, Nat>, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, Got>>, acc: List<&2, St>) -> List<&2, St>:
  match rest:
    case SNil{}:
      run.push(need, St{pos, left, word, SNil{}, caps}, acc)
    case SCon{+x, +t}:
      +a = run.push(need, St{pos, left, word, SCon{x, t}, caps}, acc)
      or_else(Bool.and(run.room(room), is_in(c, x)), k => run.go(t, c, pred(need), run.less(room), 1n+pos, pred(left), is_word(x), caps, a), a)

def run(c: Cls, need: Nat, room: Maybe<&2, Nat>, s: St) -> List<&2, St>:
  match s:
    case St{pos, left, word, rest, caps}:
      run.go(rest, c, need, room, pos, left, word, caps, Nil{})

def bound(s: St) -> Maybe<&2, St>:
  match s:
    case St{pos, left, +word, +rest, caps}:
      keep(Bool.xor(word, next_word(rest)), St{pos, left, word, rest, caps})

def begin(s: St) -> Maybe<&2, St>:
  match s:
    case St{+pos, left, word, rest, caps}:
      keep(Nat.is_eq(pos, 0n), St{pos, left, word, rest, caps})

def end(s: St) -> Maybe<&2, St>:
  match s:
    case St{pos, left, word, +rest, caps}:
      keep(String.is_empty(rest), St{pos, left, word, rest, caps})

# the place itself when min is 0 (a run or a repetition that may stop)
def zero(min: Nat, s: St) -> Maybe<&2, St>:
  match min:
    case 0n:
      Some{s}
    case 1n+m:
      None{}

# the readings of one piece that reads no inner pieces
def leaf(p: Piece, s: St) -> List<&2, St>:
  match p:
    case Lit{u}:
      m2l(lit(u, False{}, s))
    case Fold{u}:
      m2l(lit(u, True{}, s))
    case Run{c, need, room}:
      run(c, need, room, s)
    case Cap{ps}:
      Nil{}
    case Opt{ps}:
      Nil{}
    case Alt{a, b}:
      Nil{}
    case Many{ps, min}:
      Nil{}
    case Ahead{ps, neg}:
      Nil{}
    case Same{k}:
      m2l(same(k, s))
    case Bound{}:
      m2l(bound(s))
    case Begin{}:
      m2l(begin(s))
    case End{}:
      m2l(end(s))

# Captures
# --------

# how many captures the pieces ps open
def ncaps(ps: List<&2, Piece>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      match p:
        case Lit{u}:
          ncaps(t)
        case Fold{u}:
          ncaps(t)
        case Run{c, need, room}:
          ncaps(t)
        case Cap{i}:
          1n+Nat.add(ncaps(i), ncaps(t))
        case Opt{i}:
          Nat.add(ncaps(i), ncaps(t))
        case Alt{a, b}:
          Nat.add(Nat.add(ncaps(a), ncaps(b)), ncaps(t))
        case Many{i, min}:
          Nat.add(ncaps(i), ncaps(t))
        case Ahead{i, neg}:
          Nat.add(ncaps(i), ncaps(t))
        case Same{k}:
          ncaps(t)
        case Bound{}:
          ncaps(t)
        case Begin{}:
          ncaps(t)
        case End{}:
          ncaps(t)

# each reading, capture k set to the text from at (the text from there on:
# from) to the reading's place
def close(xs: List<&2, St>, +k: Nat, +at: Nat, +from: String) -> List<&2, St>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match x:
        case St{+pos, left, word, rest, caps}:
          St{pos, left, word, rest, List.set(&2, Maybe<&2, Got>, caps, k, Some{Got{at, pos, from}})} <> close(t, k, at, from)

def grew.if(b: Bool, x: St, t: List<&2, St>) -> List<&2, St>:
  match b:
    case True{}:
      x <> t
    case False{}:
      t

# the readings with fewer than l chars after them (they read at least one
# char past a place with l chars after it)
def grew(+l: Nat, xs: List<&2, St>) -> List<&2, St>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match x:
        case St{pos, +left, word, rest, caps}:
          grew.if(Nat.is_lt(left, l), St{pos, left, word, rest, caps}, grew(l, t))

# Every reading
# -------------

def place(s: St) -> Nat:
  match s:
    case St{pos, left, word, rest, caps}:
      pos

def remain(s: St) -> Nat:
  match s:
    case St{pos, left, word, rest, caps}:
      left

def after(s: St) -> String:
  match s:
    case St{pos, left, word, rest, caps}:
      rest


def ahead.if(neg: Bool, xs: List<&2, St>, s: St) -> List<&2, St>:
  m2l(keep(Bool.xor(neg, Bool.not(List.is_empty(&2, St, xs))), s))

# every reading of the pieces ps from each place of L in turn (captures
# of ps numbered from base + 1), in priority order, all of them computed;
# the fuel f bounds the rounds of a repetition (a further round is read
# with one less)
def go(f: Nat, ps: List<&2, Piece>, L: List<&2, St>, +base: Nat) -> List<&2, St>:
  match f:
    case 0n:
      Nil{}
    case 1n++g:
      match ps:
        case Nil{}:
          L
        case p <> +t:
          match p:
            case Lit{+u}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Lit{u}, s), base), go(1n+g, Lit{u} <> t, rest, base))
            case Fold{+u}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Fold{u}, s), base), go(1n+g, Fold{u} <> t, rest, base))
            case Run{+c, +need, +room}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Run{c, need, room}, s), base), go(1n+g, Run{c, need, room} <> t, rest, base))
            case Cap{+i}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, close(go(1n+g, i, [s], 1n+base), base, place(s), after(s)), 1n+Nat.add(base, ncaps(i))), go(1n+g, Cap{i} <> t, rest, base))
            case Opt{+i}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, List.append(&2, St, go(1n+g, i, [s], base), [s]), Nat.add(base, ncaps(i))), go(1n+g, Opt{i} <> t, rest, base))
            case Alt{+a, +b}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, List.append(&2, St, go(1n+g, a, [s], base), go(1n+g, b, [s], Nat.add(base, ncaps(a)))), Nat.add(Nat.add(base, ncaps(a)), ncaps(b))), go(1n+g, Alt{a, b} <> t, rest, base))
            case Many{+i, +min}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, List.append(&2, St, go(g, [Many{i, pred(min)}], grew(remain(s), go(1n+g, i, [s], base)), base), m2l(zero(min, s))), Nat.add(base, ncaps(i))), go(1n+g, Many{i, min} <> t, rest, base))
            case Ahead{+i, +neg}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, ahead.if(neg, go(1n+g, i, [s], base), s), Nat.add(base, ncaps(i))), go(1n+g, Ahead{i, neg} <> t, rest, base))
            case Same{+k}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Same{k}, s), base), go(1n+g, Same{k} <> t, rest, base))
            case Bound{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Bound{}, s), base), go(1n+g, Bound{} <> t, rest, base))
            case Begin{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(Begin{}, s), base), go(1n+g, Begin{} <> t, rest, base))
            case End{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, St, go(1n+g, t, leaf(End{}, s), base), go(1n+g, End{} <> t, rest, base))

# The matcher
# -----------
# The first reading is found by backtracking: the pieces are read from a
# place one way at a time, the pieces still to read after them kept as a
# stack of frames, and the next way is tried only when this one has no
# reading whose end condition holds.

# The matcher
# -----------
# The searches find a place's first reading by backtracking: the pieces
# are read one way at a time, what is still to read after them kept as a
# stack of frames, and the next way is tried only when this one has no
# reading whose end condition holds. Its readings are those of every
# fuel past the count of chars after the place (law shape_fuel_enough).

# a place to read from, or an answer already found
type W is Data:
  # read from the place s
  Want{s: St}
  # the answer r was found before: nothing more is read
  Have{r: St}
  # no place: no reading
  Nothing{}

def want(m: Maybe<&2, St>) -> W:
  match m:
    case None{}:
      Nothing{}
    case Some{s}:
      Want{s}

# the answer x when there is one, else the place m
def prefer(x: Maybe<&2, St>, m: Maybe<&2, St>) -> W:
  match x:
    case None{}:
      want(m)
    case Some{r}:
      Have{r}

# where the captures of a list of pieces are numbered from: n, after the
# captures of the lists skipped since (counted only when a capture needs
# its number)
type Base is Data:
  BAt{n: Nat}
  BAfter{b: Base, ps: List<&2, Piece>}

def val(b: Base) -> Nat:
  match b:
    case BAt{n}:
      n
    case BAfter{c, ps}:
      Nat.add(val(c), ncaps(ps))

# what is still to read after the pieces in hand, innermost first
type Fr is Data:
  # nothing: the reading is done
  FEnd{}
  # the pieces ps, captures from b, then k
  FSeq{ps: List<&2, Piece>, b: Base, k: Fr}
  # set capture n to the chars from char at (the text from there: from),
  # then k
  FCap{n: Nat, at: Nat, from: String, k: Fr}
  # a round of the repetition that heads ps (Many{i, min} <> t, captures
  # from b) ended: when it read a char past the place with l chars after
  # it, the repetition goes on with one round less asked, then t, then k
  FRound{ps: List<&2, Piece>, b: Base, l: Nat, k: Fr}

# the pieces ps (captures from b) before the frames K: none for no pieces
def push(ps: List<&2, Piece>, b: Base, K: Fr) -> Fr:
  match ps:
    case Nil{}:
      K
    case p <> t:
      FSeq{p <> t, b, K}

# Many: the pieces after a round of the repetition that heads ps (ps
# itself when it asks for no more rounds)
def many.next(+ps: List<&2, Piece>) -> List<&2, Piece>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case Many{i, min}:
          match min:
            case 0n:
              ps
            case 1n+k:
              Many{i, k} <> t
        case _:
          ps

# the readings xs taken through the frames K, every one computed with
# fuel f (the matcher's fallback)
def frames(+f: Nat, K: Fr, xs: List<&2, St>) -> List<&2, St>:
  match K:
    case FEnd{}:
      xs
    case FSeq{t, b, k}:
      frames(f, k, go(f, t, xs, val(b)))
    case FCap{n, at, from, k}:
      frames(f, k, close(xs, n, at, from))
    case FRound{ps, b, l, k}:
      frames(f, k, go(f, many.next(ps), grew(l, xs), val(b)))

def first_end.if(ends: Bool, empty: Bool, x: St, m: Maybe<&2, St>) -> Maybe<&2, St>:
  match ends empty:
    case False{} _:
      Some{x}
    case True{} True{}:
      Some{x}
    case True{} False{}:
      m

# the first reading of xs whose end condition holds (ends: the text must
# end there)
def first_end(+ends: Bool, xs: List<&2, St>) -> Maybe<&2, St>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      match x:
        case St{pos, left, word, +rest, caps}:
          first_end.if(ends, String.is_empty(rest), St{pos, left, word, rest, caps}, first_end(ends, t))

# a place every piece and frame has read: a reading, unless it must end
# the text and does not
def done(ends: Bool, s: St) -> Maybe<&2, St>:
  match ends:
    case False{}:
      Some{s}
    case True{}:
      end(s)

# the matcher's answer with no budget left: every reading computed, fuel
# one past the place's count of chars after it
def out(w: W, ps: List<&2, Piece>, b: Base, K: Fr, ends: Bool) -> Maybe<&2, St>:
  match w:
    case Want{+s}:
      +f = {1n+remain(s) : Nat}
      first_end(ends, frames(f, K, go(f, ps, [s], val(b))))
    case Have{r}:
      Some{r}
    case Nothing{}:
      None{}

# Run: the place after one more char of the class c, when max allows one
def run.step(c: Cls, max: Maybe<&2, Nat>, s: St) -> Maybe<&2, St>:
  match s:
    case St{pos, left, word, rest, caps}:
      match rest:
        case SNil{}:
          None{}
        case SCon{+x, t}:
          keep(Bool.and(run.room(max), is_in(c, x)), St{1n+pos, pred(left), is_word(x), t, caps})

# Run: the pieces after one more char of the run Run{c, min, max} before
# t (ps: those pieces, themselves when the run has no bounds)
def run.next(min: Nat, max: Maybe<&2, Nat>, c: Cls, t: List<&2, Piece>, ps: List<&2, Piece>) -> List<&2, Piece>:
  match min:
    case 0n:
      match max:
        case None{}:
          ps
        case Some{n}:
          Run{c, 0n, Some{pred(n)}} <> t
    case 1n+k:
      Run{c, k, run.less(max)} <> t

# Many: the place, when a round read a char past a place with l chars
# after it
def moved(+l: Nat, s: St) -> Maybe<&2, St>:
  match s:
    case St{pos, +left, word, rest, caps}:
      keep(Nat.is_lt(left, l), St{pos, left, word, rest, caps})

# Cap: the place with capture k set to the chars from char at (the text
# from there: from) to it
def set(s: St, +k: Nat, at: Nat, from: String) -> St:
  match s:
    case St{+pos, left, word, rest, caps}:
      St{pos, left, word, rest, List.set(&2, Maybe<&2, Got>, caps, k, Some{Got{at, pos, from}})}

# Ahead: the place itself when the inner pieces have a reading (m), or
# when neg and they have none
def ahead.at(neg: Bool, m: Maybe<&2, St>, s: St) -> Maybe<&2, St>:
  match m:
    case None{}:
      keep(neg, s)
    case Some{x}:
      keep(Bool.not(neg), s)

# The first reading of the pieces ps from the place of w, then of the
# frames K, whose end condition holds (ends); w's answer when it has one.
# Budget T: each step costs one; with none left the rest is read by go.
def seek(T: Nat, w: W, +ps: List<&2, Piece>, +b: Base, +K: Fr, +ends: Bool) -> Maybe<&2, St>:
  match T:
    case 0n:
      out(w, ps, b, K, ends)
    case 1n++st:
      match w:
        case Have{r}:
          Some{r}
        case Nothing{}:
          None{}
        case Want{+s}:
          match ps:
            case Nil{}:
              match K:
                case FEnd{}:
                  done(ends, s)
                case FSeq{t, c, k}:
                  seek(st, Want{s}, t, c, k, ends)
                case FCap{n, at, from, k}:
                  seek(st, Want{set(s, n, at, from)}, Nil{}, b, k, ends)
                case FRound{q, c, l, k}:
                  seek(st, want(moved(l, s)), many.next(q), c, k, ends)
            case q <> +t:
              match q:
                case Lit{u}:
                  seek(st, want(lit(u, False{}, s)), t, b, K, ends)
                case Fold{u}:
                  seek(st, want(lit(u, True{}, s)), t, b, K, ends)
                case Run{+c, +min, +max}:
                  seek(st, prefer(seek(st, want(run.step(c, max, s)), run.next(min, max, c, t, ps), b, K, ends), zero(min, s)), t, b, K, ends)
                case Cap{+i}:
                  +n = val(b)
                  seek(st, Want{s}, i, BAt{1n+n}, FCap{n, place(s), after(s), push(t, BAfter{BAt{1n+n}, i}, K)}, ends)
                case Opt{+i}:
                  +c = {BAfter{b, i} : Base}
                  seek(st, prefer(seek(st, Want{s}, i, b, push(t, c, K), ends), Some{s}), t, c, K, ends)
                case Alt{+a, +c}:
                  +d = {BAfter{b, a} : Base}
                  +K2 = {push(t, BAfter{d, c}, K) : Fr}
                  seek(st, prefer(seek(st, Want{s}, a, b, K2, ends), Some{s}), c, d, K2, ends)
                case Many{+i, min}:
                  seek(st, prefer(seek(st, Want{s}, i, b, FRound{ps, b, remain(s), K}, ends), zero(min, s)), t, BAfter{b, i}, K, ends)
                case Ahead{+i, neg}:
                  seek(st, want(ahead.at(neg, seek(st, Want{s}, i, b, FEnd{}, False{}), s)), t, BAfter{b, i}, K, ends)
                case Same{k}:
                  seek(st, want(same(k, s)), t, b, K, ends)
                case Bound{}:
                  seek(st, want(bound(s)), t, b, K, ends)
                case Begin{}:
                  seek(st, want(begin(s)), t, b, K, ends)
                case End{}:
                  seek(st, want(end(s)), t, b, K, ends)

# the budget of a search from the place s: steps before the matcher falls
# back to computing every reading, 64 per char after s (a real search
# takes a few; a small budget keeps the kernel's check of the examples
# short)
def budget(s: St) -> Nat:
  Nat.mul(64n, 1n+remain(s))

# Answers
# -------

# the first reading of the pieces ps from the place s whose end condition
# holds (ends: it must end the text), every reading computed with fuel f
def at(f: Nat, ps: List<&2, Piece>, ends: Bool, s: St) -> Maybe<&2, St>:
  first_end(ends, go(f, ps, [s], 0n))

# the same found by the matcher, fuel past the place's count of chars
# after it
def first_at(+ps: List<&2, Piece>, +ends: Bool, +s: St) -> Maybe<&2, St>:
  seek(budget(s), Want{s}, ps, BAt{0n}, FEnd{}, ends)

def none_caps(n: Nat) -> List<&2, Maybe<&2, Got>>:
  List.replicate(Maybe<&2, Got>, n, None{})

def got_text(g: Maybe<&2, Got>) -> Maybe<&2, String>:
  match g:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Got{at, to, from}:
          Some{String.take(from, Nat.sub(to, at))}

def texts(cs: List<&2, Maybe<&2, Got>>) -> List<&2, Maybe<&2, String>>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      got_text(c) <> texts(t)

# the fit of a reading r that started at char p
def fit(p: Nat, r: St) -> Fit:
  match r:
    case St{pos, left, word, rest, caps}:
      Fit{p, pos, texts(caps)}

def find.try(r: Maybe<&2, St>, +p: Nat, more: Unit -> Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match r:
    case None{}:
      more(Unit{})
    case Some{x}:
      Some{Hit{x, p}}

def find.next(st: Start, more: Unit -> Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match st:
    case AtStart{}:
      None{}
    case Anywhere{}:
      more(Unit{})

# the first reading at the first place from the place (pos chars before
# it, left after it, word: the char before it is a word char, the text
# from it on) on where one holds, and that place (AtStart: only the
# first); every reading computed with fuel f
def find.go(text: String, +f: Nat, +st: Start, +ps: List<&2, Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, Got>>) -> Maybe<&2, Hit>:
  match text:
    case SNil{}:
      find.try(at(f, ps, ends, St{pos, left, word, SNil{}, caps}), pos, k => None{})
    case SCon{+x, +t}:
      find.try(at(f, ps, ends, St{pos, left, word, SCon{x, t}, caps}), pos, k => find.next(st, j => find.go(t, f, st, ps, ends, 1n+pos, pred(left), is_word(x), caps)))

# a place to search from: the text from it on, pos chars before it, left
# after it, whether the char before it is a word char
type At is Data:
  At{text: String, pos: Nat, left: Nat, word: Bool}

# the leftmost fit of the shape sh from the place a on; f: fuel past the
# count of chars after a
def find(f: Nat, sh: Shape, a: At) -> Maybe<&2, Hit>:
  match sh:
    case Shape{st, +ps, ends}:
      match a:
        case At{text, pos, left, word}:
          find.go(text, f, st, ps, ends, pos, left, word, none_caps(ncaps(ps)))

# find.go, each place's answer found by the matcher
def first.find(text: String, +st: Start, +ps: List<&2, Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, Got>>) -> Maybe<&2, Hit>:
  match text:
    case SNil{}:
      find.try(first_at(ps, ends, St{pos, left, word, SNil{}, caps}), pos, k => None{})
    case SCon{+x, +t}:
      find.try(first_at(ps, ends, St{pos, left, word, SCon{x, t}, caps}), pos, k => find.next(st, j => first.find(t, st, ps, ends, 1n+pos, pred(left), is_word(x), caps)))

def first.hit(r: Maybe<&2, Hit>, +i: Nat, more: Unit -> Maybe<&2, Found>) -> Maybe<&2, Found>:
  match r:
    case None{}:
      more(Unit{})
    case Some{x}:
      match x:
        case Hit{s, p}:
          Some{Found{i, fit(p, s)}}

def first.shape(sh: Shape, text: String, n: Nat) -> Maybe<&2, Hit>:
  match sh:
    case Shape{st, +ps, ends}:
      first.find(text, st, ps, ends, 0n, n, False{}, none_caps(ncaps(ps)))

# the first shape of shs with a fit from the text's start (text: the
# text, n: its length), its index from i
def first.go(shs: List<&2, Shape>, +text: String, +n: Nat, +i: Nat) -> Maybe<&2, Found>:
  match shs:
    case Nil{}:
      None{}
    case sh <> t:
      first.hit(first.shape(sh, text, n), i, k => first.go(t, text, n, 1n+i))

# the first shape of the list that fits the text, its index and its fit
def first(shs: List<&2, Shape>, +text: String) -> Maybe<&2, Found>:
  first.go(shs, text, String.length(text), 0n)

# whether a shape may start at a place with pos chars before it (AtStart:
# only the text start)
def may(st: Start, +pos: Nat) -> Bool:
  match st:
    case AtStart{}:
      Nat.is_eq(pos, 0n)
    case Anywhere{}:
      True{}

# the answer at a place when it is tried, else none
def all.try(go: Bool, +ps: List<&2, Piece>, +ends: Bool, s: St) -> Maybe<&2, St>:
  match go:
    case True{}:
      first_at(ps, ends, s)
    case False{}:
      None{}

# the places past the next one a fit from char p to the reading r still
# covers (an empty fit: none)
def all.skip(+p: Nat, r: St) -> Nat:
  match r:
    case St{pos, left, word, rest, caps}:
      pred(Nat.sub(pos, p))

# at the last place: its fit, if any
def all.end(m: Maybe<&2, St>, +p: Nat) -> List<&2, Fit>:
  match m:
    case None{}:
      Nil{}
    case Some{r}:
      [fit(p, r)]

# at a place with more after it: its fit, if any, then the fits of the
# places after it (more: given how many of them the fit covers)
def all.here(m: Maybe<&2, St>, +p: Nat, skip: Nat, more: Nat -> List<&2, Fit>) -> List<&2, Fit>:
  match m:
    case None{}:
      more(pred(skip))
    case Some{+r}:
      fit(p, r) <> more(all.skip(p, r))

# the fits from the place (pos chars before it, left after it, word: the
# char before it is a word char, the text from it on) on, place by place:
# a place is tried when no earlier fit covers it (skip: how many places
# from here a fit still covers) and the shape may start there
def all.go(text: String, +st: Start, +ps: List<&2, Piece>, +ends: Bool, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, Got>>, +skip: Nat) -> List<&2, Fit>:
  match text:
    case SNil{}:
      all.end(all.try(Bool.and(Nat.is_eq(skip, 0n), may(st, pos)), ps, ends, St{pos, left, word, SNil{}, caps}), pos)
    case SCon{+x, +t}:
      all.here(all.try(Bool.and(Nat.is_eq(skip, 0n), may(st, pos)), ps, ends, St{pos, left, word, SCon{x, t}, caps}), pos, skip, k => all.go(t, st, ps, ends, 1n+pos, pred(left), is_word(x), caps, k))

# every fit of the shape sh in the text, left to right, none overlapping:
# each search starts where the previous fit ended (one char later after
# an empty fit); AtStart: only at the text start
def all(sh: Shape, +text: String) -> List<&2, Fit>:
  match sh:
    case Shape{st, +ps, ends}:
      all.go(text, st, ps, ends, 0n, String.length(text), False{}, none_caps(ncaps(ps)), 0n)
