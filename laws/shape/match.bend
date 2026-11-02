# eukhe: the laws of area shape: readings and splits

import Base
import ../../bend/shape.bend as S

# (S1) Explicit line shapes
# -------------------------
# bend/shape.bend: the matcher every shape table runs instead of a Rust
# `regex` (the tables: bend/incident_shapes.bend; the entry:
# bend/ffi_shape.bend; the searches: laws/shape/search.bend). Every text,
# place, class, list of pieces and piece is free.
#
# R1: a char is of a class Cls{set, neg, fold} exactly when the set names
#     it, or fold holds and the set names its other case (an ASCII letter
#     A-Z and a-z are each other's other case; any other char has none),
#     the answer turned around when neg holds. The set Codes names a char
#     whose code is in one of its ranges (both ends in); Space names the
#     Unicode White_Space chars: U+0009..U+000D, U+0020, U+0085, U+00A0,
#     U+1680, U+2000..U+200A, U+2028, U+2029, U+202F, U+205F, U+3000.
# R2: a word char is an ASCII letter, an ASCII digit or `_` (Rust's `\b`
#     and `\w` take the Unicode word chars, its `\d` the Unicode digits:
#     an intended difference).
# R3: a place is the count of chars before it, the count of chars after
#     it, whether the char before it is a word char (no at the text
#     start), the text from it on, and the captures read so far (one entry
#     each, from capture 1 on; a capture: the char counts where it starts
#     and ends and the text from its start). Reading one char x moves to
#     the next place: one more char before it, one less after it (never
#     below 0), x before it, the text after x, the captures kept.
# R4: the readings of a list of pieces from a place, in priority order:
#     no pieces: the place itself; a piece p then the pieces t: for each
#     reading of p in its order, the readings of t from there. The
#     readings of one piece:
#     - Lit s: the place after the chars of s, when the text goes on with
#       them; Fold s: the same, each char equal to the char of s once
#       ASCII capitals are read as small letters;
#     - Run c min max: for each run of chars of the class c the text goes
#       on with, of at least min and at most max chars (None: no limit),
#       the longest run first, the place after it;
#     - Cap ps: each reading of ps, its capture (the next number in the
#       order the Caps of the shape open, counting the Caps inside ps
#       after it) set to the chars from the place to the reading;
#     - Opt ps: the readings of ps, then the place itself;
#     - Alt a b: the readings of a, then those of b (the Caps of b counted
#       after those of a);
#     - Many ps min: for each reading of ps that read at least one char
#       (fewer chars after it than after the place), the readings of
#       Many ps (min - 1, never below 0) from there; then the place itself
#       when min is 0;
#     - Ahead ps neg: the place itself when ps has a reading from it
#       (neg: when it has none), its captures as they were;
#     - Same k: the place after the chars capture k took (k from 1; when
#       its text is shorter than its counts say, all of it), when capture
#       k was taken and the text goes on with them (k = 0: none);
#     - Bound: the place itself when exactly one of the char before it
#       and the char after it is a word char (no char: none);
#     - Begin: the place itself when no char is before it; End: the place
#       itself when the text from it is empty.
#     A fuel f bounds the rounds of a Many: with no fuel there is no
#     reading, and each further round of a Many is read with one less;
#     the readings of a place are those of fuel one past its count of
#     chars after it (laws shape_split_*: then they are every split).
# R5: the answer of a list of pieces at a place is the first of its
#     readings whose end condition holds (ends: the text from it is
#     empty), none when there is none.
# R6: a split of the text from a place for a list of pieces is one part
#     per piece, in order (a Many: one part per round, each reading at
#     least one char, then one part for its end, its rounds at least
#     min): a Lit's part is its text, a Fold's equals it once capitals are
#     read as small, a Run's part has at least min and at most max chars,
#     each of the class, a Same's part is the text the capture took, a
#     Bound's, Begin's or End's part is empty where its condition holds;
#     the text goes on with each part; a Cap's part is the split of its
#     pieces, captured; an Opt's part is the split of its pieces or
#     nothing; an Alt's part is a split of one option; a positive Ahead's
#     part is a split of its pieces, reading nothing; a negative Ahead
#     holds where its pieces have no reading. The readings of a place are
#     exactly the places its splits reach.

# Spec helpers
# ------------

def sp_code_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# R1: a code in one of the ranges
def sp_codes(rs: List<&2, S.Rg>, +x: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case S.Rg{lo, hi}:
          Bool.or(sp_code_in(x, lo, hi), sp_codes(t, x))

# R1: the Unicode White_Space codes
def sp_ws(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

# R1: the codes a set names
def sp_names(st: S.Chars, +x: U32) -> Bool:
  match st:
    case S.Codes{rs}:
      sp_codes(rs, x)
    case S.Space{}:
      sp_ws(x)

def sp_other.at(+x: U32, up: Bool, low: Bool) -> U32:
  match up low:
    case True{} _:
      U32.add(x, 32)
    case False{} True{}:
      U32.sub(x, 32)
    case False{} False{}:
      x

# R1: the other case of an ASCII letter, any other code itself
def sp_other(+x: U32) -> U32:
  sp_other.at(x, sp_code_in(x, 65, 90), sp_code_in(x, 97, 122))

# R1: whether the char c is of the class k
def sp_cls(k: S.Cls, c: Char) -> Bool:
  match k:
    case S.Cls{+st, neg, fold}:
      match c:
        case Chr{+x}:
          Bool.xor(neg, Bool.or(sp_names(st, x), Bool.and(fold, sp_names(st, sp_other(x)))))

# R2: a word char: a-z (97-122), A-Z (65-90), 0-9 (48-57) or `_` (95)
def sp_word(c: Char) -> Bool:
  match c:
    case Chr{+v}:
      Bool.or(sp_code_in(v, 97, 122), Bool.or(sp_code_in(v, 65, 90), Bool.or(sp_code_in(v, 48, 57), U32.is_eq(v, 95))))

# R4: a code with an ASCII capital read as its small letter
def sp_small(+x: U32) -> U32:
  sp_other.at(x, sp_code_in(x, 65, 90), False{})

# R4: the chars x and y are equal (ci: once capitals are read as small)
def sp_ch_eq(ci: Bool, x: Char, y: Char) -> Bool:
  match ci:
    case True{}:
      match x y:
        case Chr{a} Chr{b}:
          U32.is_eq(sp_small(a), sp_small(b))
    case False{}:
      match x y:
        case Chr{a} Chr{b}:
          U32.is_eq(a, b)

# one less, never below 0
def sp_dec(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      m

def sp_if(b: Bool, xs: List<&2, S.St>) -> List<&2, S.St>:
  match b:
    case True{}:
      xs
    case False{}:
      Nil{}

def sp_text(s: S.St) -> String:
  match s:
    case S.St{pos, left, word, rest, caps}:
      rest

def sp_pos(s: S.St) -> Nat:
  match s:
    case S.St{pos, left, word, rest, caps}:
      pos

def sp_left(s: S.St) -> Nat:
  match s:
    case S.St{pos, left, word, rest, caps}:
      left

# R4: Lit, Fold: the place after the chars of u (ci: Fold)
def sp_eat(u: String, +ci: Bool, s: S.St) -> List<&2, S.St>:
  match u:
    case SNil{}:
      [s]
    case SCon{+y, v}:
      match s:
        case S.St{pos, left, word, rest, caps}:
          match rest:
            case SNil{}:
              Nil{}
            case SCon{+x, t}:
              sp_if(sp_ch_eq(ci, x, y), sp_eat(v, ci, S.St{1n+pos, sp_dec(left), sp_word(x), t, caps}))

# R4: whether a run that read some chars may read one more (max: None
# means no limit)
def sp_room(max: Maybe<&2, Nat>) -> Bool:
  match max:
    case None{}:
      True{}
    case Some{n}:
      match n:
        case 0n:
          False{}
        case 1n+m:
          True{}

def sp_less(max: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match max:
    case None{}:
      None{}
    case Some{n}:
      Some{sp_dec(n)}

def sp_zero(n: Nat, s: S.St) -> List<&2, S.St>:
  match n:
    case 0n:
      [s]
    case 1n+m:
      Nil{}

# R4: Run: the places after the runs of chars of c from the text rest, the
# longest first; min more chars must come, max more may
def sp_run.go(rest: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, word: Bool, +caps: List<&2, Maybe<&2, S.Got>>) -> List<&2, S.St>:
  match rest:
    case SNil{}:
      sp_zero(min, S.St{pos, left, word, SNil{}, caps})
    case SCon{+x, +t}:
      List.append(&2, S.St, sp_if(Bool.and(sp_room(max), sp_cls(c, x)), sp_run.go(t, c, sp_dec(min), sp_less(max), 1n+pos, sp_dec(left), sp_word(x), caps)), sp_zero(min, S.St{pos, left, word, SCon{x, t}, caps}))

def sp_run(c: S.Cls, min: Nat, max: Maybe<&2, Nat>, s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{pos, left, word, rest, caps}:
      sp_run.go(rest, c, min, max, pos, left, word, caps)

def sp_took.got(c: Maybe<&2, Maybe<&2, S.Got>>) -> Maybe<&2, String>:
  match c:
    case None{}:
      None{}
    case Some{m}:
      match m:
        case None{}:
          None{}
        case Some{g}:
          match g:
            case S.Got{at, to, from}:
              Some{String.take(from, Nat.sub(to, at))}

# R4: Same: the chars capture k took (k from 1)
def sp_took(k: Nat, caps: List<&2, Maybe<&2, S.Got>>) -> Maybe<&2, String>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      sp_took.got(List.get(&2, Maybe<&2, S.Got>, caps, j))

def sp_same.at(m: Maybe<&2, String>, s: S.St) -> List<&2, S.St>:
  match m:
    case None{}:
      Nil{}
    case Some{u}:
      sp_eat(u, False{}, s)

def sp_same(k: Nat, s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{pos, left, word, rest, +caps}:
      sp_same.at(sp_took(k, caps), S.St{pos, left, word, rest, caps})

# R4: Bound, Begin, End
def sp_starts_word(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{x, t}:
      sp_word(x)

def sp_bound(s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{pos, left, +word, +rest, caps}:
      sp_if(Bool.xor(word, sp_starts_word(rest)), [S.St{pos, left, word, rest, caps}])

def sp_begin(s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{+pos, left, word, rest, caps}:
      sp_if(Nat.is_eq(pos, 0n), [S.St{pos, left, word, rest, caps}])

def sp_end(s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{pos, left, word, +rest, caps}:
      sp_if(String.is_empty(rest), [S.St{pos, left, word, rest, caps}])

# R4: how many Caps the pieces ps hold, inner ones too
def sp_ncaps(ps: List<&2, S.Piece>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case p <> t:
      match p:
        case S.Lit{u}:
          sp_ncaps(t)
        case S.Fold{u}:
          sp_ncaps(t)
        case S.Run{c, min, max}:
          sp_ncaps(t)
        case S.Cap{i}:
          1n+Nat.add(sp_ncaps(i), sp_ncaps(t))
        case S.Opt{i}:
          Nat.add(sp_ncaps(i), sp_ncaps(t))
        case S.Alt{a, b}:
          Nat.add(Nat.add(sp_ncaps(a), sp_ncaps(b)), sp_ncaps(t))
        case S.Many{i, min}:
          Nat.add(sp_ncaps(i), sp_ncaps(t))
        case S.Ahead{i, neg}:
          Nat.add(sp_ncaps(i), sp_ncaps(t))
        case S.Same{k}:
          sp_ncaps(t)
        case S.Bound{}:
          sp_ncaps(t)
        case S.Begin{}:
          sp_ncaps(t)
        case S.End{}:
          sp_ncaps(t)

# R4: Cap: each reading with capture entry k set to the chars from char
# at (the text from there: from) to it
def sp_cap(xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String) -> List<&2, S.St>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match x:
        case S.St{+pos, left, word, rest, caps}:
          S.St{pos, left, word, rest, List.set(&2, Maybe<&2, S.Got>, caps, k, Some{S.Got{at, pos, from}})} <> sp_cap(t, k, at, from)

# R4: Many: the readings with fewer than l chars after them (they read at
# least one char past a place with l chars after it)
def sp_moved(+l: Nat, xs: List<&2, S.St>) -> List<&2, S.St>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      +y = x
      List.append(&2, S.St, sp_if(Nat.is_lt(sp_left(y), l), [y]), sp_moved(l, t))

# R4: Ahead: the place when ps has a reading (neg: none)
def sp_ahead(neg: Bool, xs: List<&2, S.St>, s: S.St) -> List<&2, S.St>:
  match xs:
    case Nil{}:
      sp_if(neg, [s])
    case x <> t:
      sp_if(Bool.not(neg), [s])

# R4: the readings of the pieces ps from each place of L in turn (their
# captures numbered from entry base on), fuel f
def sp_reads(f: Nat, ps: List<&2, S.Piece>, L: List<&2, S.St>, +base: Nat) -> List<&2, S.St>:
  match f:
    case 0n:
      Nil{}
    case 1n++g:
      match ps:
        case Nil{}:
          L
        case p <> +t:
          match p:
            case S.Lit{+u}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_eat(u, False{}, s), base), sp_reads(1n+g, S.Lit{u} <> t, rest, base))
            case S.Fold{+u}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_eat(u, True{}, s), base), sp_reads(1n+g, S.Fold{u} <> t, rest, base))
            case S.Run{+c, +min, +max}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_run(c, min, max, s), base), sp_reads(1n+g, S.Run{c, min, max} <> t, rest, base))
            case S.Cap{+i}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_cap(sp_reads(1n+g, i, [s], 1n+base), base, sp_pos(s), sp_text(s)), 1n+Nat.add(base, sp_ncaps(i))), sp_reads(1n+g, S.Cap{i} <> t, rest, base))
            case S.Opt{+i}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, List.append(&2, S.St, sp_reads(1n+g, i, [s], base), [s]), Nat.add(base, sp_ncaps(i))), sp_reads(1n+g, S.Opt{i} <> t, rest, base))
            case S.Alt{+a, +b}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, List.append(&2, S.St, sp_reads(1n+g, a, [s], base), sp_reads(1n+g, b, [s], Nat.add(base, sp_ncaps(a)))), Nat.add(Nat.add(base, sp_ncaps(a)), sp_ncaps(b))), sp_reads(1n+g, S.Alt{a, b} <> t, rest, base))
            case S.Many{+i, +min}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, List.append(&2, S.St, sp_reads(g, [S.Many{i, sp_dec(min)}], sp_moved(sp_left(s), sp_reads(1n+g, i, [s], base)), base), sp_zero(min, s)), Nat.add(base, sp_ncaps(i))), sp_reads(1n+g, S.Many{i, min} <> t, rest, base))
            case S.Ahead{+i, +neg}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_ahead(neg, sp_reads(1n+g, i, [s], base), s), Nat.add(base, sp_ncaps(i))), sp_reads(1n+g, S.Ahead{i, neg} <> t, rest, base))
            case S.Same{+k}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_same(k, s), base), sp_reads(1n+g, S.Same{k} <> t, rest, base))
            case S.Bound{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_bound(s), base), sp_reads(1n+g, S.Bound{} <> t, rest, base))
            case S.Begin{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_begin(s), base), sp_reads(1n+g, S.Begin{} <> t, rest, base))
            case S.End{}:
              match L:
                case Nil{}:
                  Nil{}
                case +s <> rest:
                  List.append(&2, S.St, sp_reads(1n+g, t, sp_end(s), base), sp_reads(1n+g, S.End{} <> t, rest, base))

# R4: the readings of a place: fuel one past the length of its text, the
# captures of the pieces numbered from 1
def sp_readings(ps: List<&2, S.Piece>, +s: S.St) -> List<&2, S.St>:
  sp_reads(1n+sp_left(s), ps, [s], 0n)

# R5: the readings whose end condition holds
def sp_keep(ends: Bool, xs: List<&2, S.St>) -> List<&2, S.St>:
  match ends:
    case False{}:
      xs
    case True{}:
      match xs:
        case Nil{}:
          Nil{}
        case x <> t:
          +y = x
          List.append(&2, S.St, sp_if(String.is_empty(sp_text(y)), [y]), sp_keep(True{}, t))

def sp_head(xs: List<&2, S.St>) -> Maybe<&2, S.St>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      Some{x}

# R5: the answer at the place s: its first reading whose end condition
# holds
def sp_answer(f: Nat, ps: List<&2, S.Piece>, ends: Bool, s: S.St) -> Maybe<&2, S.St>:
  sp_head(sp_keep(ends, sp_reads(f, ps, [s], 0n)))

# R6: a split of a list of pieces: one part per piece, in order (a Many:
# one part per round, then one for its end)
type Part is Data:
  # took: an Opt taken, an Alt's first option, one more round of a Many;
  # u: the chars of a Lit, Fold, Run or Same (none for Bound, Begin,
  # End); ws: the parts of the inner pieces of a Cap, an Opt taken, an
  # Alt's option, a Many's round, a positive Ahead
  Part{took: Bool, u: String, ws: List<&2, Part>}

# R6: the place x is one of the places xs
def sp_has(x: S.St, xs: List<&2, S.St>) -> Data:
  match xs:
    case Nil{}:
      Empty
    case h <> t:
      Either<&2, &2, {h == x : S.St}, sp_has(x, t)>

# R6: the place r is one of the readings of the pieces ps at the place s
def sp_reached(r: S.St, ps: List<&2, S.Piece>, s: S.St) -> Data:
  sp_has(r, sp_readings(ps, s))

def sp_when(b: Bool, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

# R6: the place after the chars u, when the text goes on with them
def sp_go_on(u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      sp_head(sp_eat(u, False{}, s))

# R6: the chars of u equal those of v, one by one (ci: once capitals are
# read as small)
def sp_text_eq(+ci: Bool, u: String, v: String) -> Bool:
  match u v:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, b}:
      False{}
    case SCon{x, a} SNil{}:
      False{}
    case SCon{x, a} SCon{y, b}:
      Bool.and(sp_ch_eq(ci, x, y), sp_text_eq(ci, a, b))

# R6: Run: every char of u is of the class c
def sp_all_cls(+c: S.Cls, u: String) -> Bool:
  match u:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_cls(c, x), sp_all_cls(c, t))

def sp_at_most(+n: Nat, max: Maybe<&2, Nat>) -> Bool:
  match max:
    case None{}:
      True{}
    case Some{k}:
      Nat.is_le(n, k)

# R6: Run: the part has at least min and at most max chars of the class
def sp_part_run(+c: S.Cls, min: Nat, max: Maybe<&2, Nat>, +u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  +n = String.length(u)
  sp_when(Bool.and(sp_all_cls(c, u), Bool.and(Nat.is_le(min, n), sp_at_most(n, max))), sp_go_on(u, m))

def sp_is(t: Maybe<&2, String>, u: String) -> Bool:
  match t:
    case None{}:
      False{}
    case Some{v}:
      sp_text_eq(False{}, v, u)

def sp_caps(s: S.St) -> List<&2, Maybe<&2, S.Got>>:
  match s:
    case S.St{pos, left, word, rest, caps}:
      caps

# R6: Same: the part is the chars capture k took
def sp_part_same(k: Nat, +u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      sp_when(sp_is(sp_took(k, sp_caps(s)), u), sp_go_on(u, Some{s}))

# R6: Bound, Begin, End: no chars, and the condition at the place
def sp_part_bound(u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      sp_when(String.is_empty(u), sp_head(sp_bound(s)))

def sp_part_begin(u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      sp_when(String.is_empty(u), sp_head(sp_begin(s)))

def sp_part_end(u: String, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      sp_when(String.is_empty(u), sp_head(sp_end(s)))

# R6: Cap: the inner parts' place r, capture entry k set to the chars from
# the place m to it
def sp_part_cap(+k: Nat, m: Maybe<&2, S.St>, r: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          sp_head(sp_cap([x], k, sp_pos(s), sp_text(s)))

def sp_pick(took: Bool, a: Maybe<&2, S.St>, b: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match took:
    case True{}:
      a
    case False{}:
      b

# R6: Many: a round that read at least one char (fewer chars after it)
def sp_part_round(m: Maybe<&2, S.St>, r: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match r:
        case None{}:
          None{}
        case Some{+x}:
          sp_when(Nat.is_lt(sp_left(x), sp_left(s)), Some{x})

# R6: Many: no more rounds, when no more are asked for
def sp_part_stop(min: Nat, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match min:
    case 0n:
      m
    case 1n+k:
      None{}

def sp_some(r: Maybe<&2, S.St>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{x}:
      True{}

# R6: Ahead: the place itself, when the inner parts r read from it (neg:
# when the inner pieces have no reading from it)
def sp_part_ahead(neg: Bool, r: Maybe<&2, S.St>, i: List<&2, S.Piece>, +base: Nat, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match neg:
    case False{}:
      match m:
        case None{}:
          None{}
        case Some{s}:
          sp_when(sp_some(r), Some{s})
    case True{}:
      match m:
        case None{}:
          None{}
        case Some{+s}:
          sp_when(List.is_empty(&2, S.St, sp_reads(1n+sp_left(s), i, [s], base)), Some{s})

def sp_split.end(ps: List<&2, S.Piece>, m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match ps:
    case Nil{}:
      m
    case p <> t:
      None{}

# R6: the place the parts ws reach when they split the text from the place
# m for the pieces ps (captures numbered from entry base on); None when
# they are no split of it
def sp_split(ws: List<&2, Part>, ps: List<&2, S.Piece>, +base: Nat, +m: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match ws:
    case Nil{}:
      sp_split.end(ps, m)
    case w <> +wt:
      match w:
        case Part{took, +u, +wi}:
          match ps:
            case Nil{}:
              None{}
            case p <> +t:
              match p:
                case S.Lit{v}:
                  sp_split(wt, t, base, sp_when(sp_text_eq(False{}, u, v), sp_go_on(u, m)))
                case S.Fold{v}:
                  sp_split(wt, t, base, sp_when(sp_text_eq(True{}, u, v), sp_go_on(u, m)))
                case S.Run{c, min, max}:
                  sp_split(wt, t, base, sp_part_run(c, min, max, u, m))
                case S.Cap{+i}:
                  sp_split(wt, t, 1n+Nat.add(base, sp_ncaps(i)), sp_part_cap(base, m, sp_split(wi, i, 1n+base, m)))
                case S.Opt{+i}:
                  sp_split(wt, t, Nat.add(base, sp_ncaps(i)), sp_pick(took, sp_split(wi, i, base, m), m))
                case S.Alt{+a, +b}:
                  sp_split(wt, t, Nat.add(Nat.add(base, sp_ncaps(a)), sp_ncaps(b)), sp_pick(took, sp_split(wi, a, base, m), sp_split(wi, b, Nat.add(base, sp_ncaps(a)), m)))
                case S.Many{+i, +min}:
                  sp_pick(took, sp_split(wt, S.Many{i, sp_dec(min)} <> t, base, sp_part_round(m, sp_split(wi, i, base, m))), sp_split(wt, t, Nat.add(base, sp_ncaps(i)), sp_part_stop(min, m)))
                case S.Ahead{+i, +neg}:
                  sp_split(wt, t, Nat.add(base, sp_ncaps(i)), sp_part_ahead(neg, sp_split(wi, i, base, m), i, base, m))
                case S.Same{k}:
                  sp_split(wt, t, base, sp_part_same(k, u, m))
                case S.Bound{}:
                  sp_split(wt, t, base, sp_part_bound(u, m))
                case S.Begin{}:
                  sp_split(wt, t, base, sp_part_begin(u, m))
                case S.End{}:
                  sp_split(wt, t, base, sp_part_end(u, m))

# Laws
# ----

# LAW shape_first_reading (R1-R5): at every place, for every fuel, list of
# pieces and end condition, the matcher answers the first reading of the
# priority-ordered list of every reading whose end condition holds
# EXCLUDES: a run that is not longest first or gives back too much, an
#   option skipped before it is tried, options in another order, fewer
#   rounds tried before more, a reading whose end condition fails taken,
#   a capture numbered or taken another way, a char of another class
#   taken, a case fold where none is asked, a word boundary of another
#   kind
law shape_first_reading:
  for +f: Nat
  for +ps: List<&2, S.Piece>
  for +ends: Bool
  for +s: S.St
  {S.at(f, ps, ends, s) == sp_answer(f, ps, ends, s) : Maybe<&2, S.St>}

# LAW shape_split_sound (R4, R6): every reading of a place is a split: the
# text from the place splits into one part per piece, each part of its
# piece, and the split reaches the reading
# EXCLUDES: a reading invented (a char of another class, an option read
#   that is no option, a round that reads nothing, a capture that took
#   other chars, a boundary or an end where there is none, an Ahead whose
#   pieces do not or do read)
law shape_split_sound:
  for +ps: List<&2, S.Piece>
  for +s: S.St
  for +r: S.St
  for h: sp_reached(r, ps, s)
  exs ws: List<&2, Part>
  {sp_split(ws, ps, 0n, Some{s}) == Some{r} : Maybe<&2, S.St>}

# LAW shape_split_complete (R4, R6): every split of the text from a place
# reaches one of its readings
# EXCLUDES: a way to read missed (a shorter run, an option skipped, the
#   second option, fewer rounds, a capture never set), a reading lost to
#   the fuel
law shape_split_complete:
  for +ps: List<&2, S.Piece>
  for +ws: List<&2, Part>
  for +s: S.St
  for +r: S.St
  for h: {sp_split(ws, ps, 0n, Some{s}) == Some{r} : Maybe<&2, S.St>}
  sp_reached(r, ps, s)
