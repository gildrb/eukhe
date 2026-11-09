# eukhe: the laws of area privacy, section session: the token map one
# session owns (bend/privacy/token.bend; eukhe-ai privacy/mod.rs
# `TokenMap`, one per session, for the session's life)

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy.bend as S
import ../../spec/harness/privacy_map.bend as Sm

# (H7) A session's tokens are its own
# -----------------------------------
# spec/README.md H7. The daemon once held one token map for every session:
# a value session A scrubbed (10.0.0.1 -> IP_1) came back into session B's
# answer when B's model wrote IP_1, and B's first IP address took IP_2.
# Each session now owns its map: it opens empty (Tk.Book.empty()) and only
# the scrubs of that session's texts, in order, each against the map the
# one before it left, change it (session below). A text is the pieces Rust
# reads (plain text and values); an answer the pieces the model wrote.
#
# R13: from the map a session's texts left, restoring any answer keeps
#      every piece, or brings a token of a class that maps back (S4) into
#      clear as a value of that class one of the session's own texts
#      holds; so a session that scrubbed nothing restores nothing. Every text
#      a session scrubs leaves with each value of a class that maps back as
#      the token of its class numbered by the value's place among the
#      distinct values of that class in the session's texts so far (that
#      text last), in the order they first appear, from 1; each credential
#      as its one-way token; plain text as it is.
#
# The spec helpers below read the raw texts and answers (has, before,
# kinds); they call no code but Tk's data types and the session fold over
# Tk.scrub (the steps Rust runs), plus S.reversible (S4) and Sm.same_class
# (class equality, by the spec's own class numbers).

# Terms
# -----

# the map of a session that scrubbed the texts xss, in order, from m: each
# text against the map the one before it left
def session.go(xss: List<&2, List<&2, Tk.Piece>>, m: Tk.Book) -> Tk.Book:
  match xss:
    case Nil{}:
      m
    case xs <> rest:
      session.go(rest, Tk.Out.m(Tk.scrub(m, xs)))

# the map a session holds after its texts xss: it opens empty
def session(xss: List<&2, List<&2, Tk.Piece>>) -> Tk.Book:
  session.go(xss, Tk.Book.empty())

# the texts of a session, one after another
def history(xss: List<&2, List<&2, Tk.Piece>>) -> List<&2, Tk.Piece>:
  List.concat(&2, Tk.Piece, xss)

# the pieces xs hold the value v of class c
def has(xs: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          has(rest, c, v)
        case Tk.Value{d, w}:
          Bool.or(Bool.and(Sm.same_class(c, d), String.eq(v, w)), has(rest, c, v))

# Terms: a restore (R13)
# ----------------------

# z is the piece y: the same kind, class, text and index
def same_seg(y: Tk.Seg, z: Tk.Seg) -> Bool:
  match y:
    case Tk.Txt{s}:
      match z:
        case Tk.Txt{t}:
          String.eq(s, t)
        case Tk.Clear{d, w}:
          False{}
        case Tk.Tok{d, j}:
          False{}
        case Tk.Hash{d, w}:
          False{}
    case Tk.Clear{c, v}:
      match z:
        case Tk.Txt{t}:
          False{}
        case Tk.Clear{d, w}:
          Bool.and(Sm.same_class(c, d), String.eq(v, w))
        case Tk.Tok{d, j}:
          False{}
        case Tk.Hash{d, w}:
          False{}
    case Tk.Tok{c, i}:
      match z:
        case Tk.Txt{t}:
          False{}
        case Tk.Clear{d, w}:
          False{}
        case Tk.Tok{d, j}:
          Bool.and(Sm.same_class(c, d), Nat.is_eq(i, j))
        case Tk.Hash{d, w}:
          False{}
    case Tk.Hash{c, v}:
      match z:
        case Tk.Txt{t}:
          False{}
        case Tk.Clear{d, w}:
          False{}
        case Tk.Tok{d, j}:
          False{}
        case Tk.Hash{d, w}:
          Bool.and(Sm.same_class(c, d), String.eq(v, w))

# z brings the token y into clear as a value h holds: y a token of a class
# that maps back, z a clear value of the same class, and h holds that value
# in that class
def brought(h: List<&2, Tk.Piece>, y: Tk.Seg, z: Tk.Seg) -> Bool:
  match y:
    case Tk.Txt{s}:
      False{}
    case Tk.Clear{c, v}:
      False{}
    case Tk.Tok{c, i}:
      match z:
        case Tk.Txt{t}:
          False{}
        case Tk.Clear{+d, w}:
          Bool.and(Bool.and(Sm.same_class(c, d), S.reversible(d)), has(h, d, w))
        case Tk.Tok{d, j}:
          False{}
        case Tk.Hash{d, w}:
          False{}
    case Tk.Hash{c, v}:
      False{}

# zs is ys, piece for piece, each piece kept or brought into clear as a
# value h holds
def all_came(+h: List<&2, Tk.Piece>, ys: List<&2, Tk.Seg>, zs: List<&2, Tk.Seg>) -> Bool:
  match ys:
    case Nil{}:
      match zs:
        case Nil{}:
          True{}
        case z <> zr:
          False{}
    case +y <> yr:
      match zs:
        case Nil{}:
          False{}
        case +z <> zr:
          Bool.and(Bool.or(same_seg(y, z), brought(h, y, z)), all_came(h, yr, zr))

# Terms: the numbers of a session's values (R13)
# ----------------------------------------------

def before.at(hit: Bool, +d: Tk.Class, +w: String, rest: List<&2, Tk.Piece>) -> List<&2, Tk.Piece>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      Tk.Value{d, w} <> rest

# the pieces of xs before its first value v of class c (all of xs when it
# holds none)
def before(xs: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> List<&2, Tk.Piece>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Plain{s} <> before(rest, c, v)
        case Tk.Value{+d, +w}:
          before.at(Bool.and(Sm.same_class(c, d), String.eq(v, w)), d, w, before(rest, c, v))

def kinds.at(last: Bool, n: Nat) -> Nat:
  match last:
    case True{}:
      1n+n
    case False{}:
      n

# how many distinct values of class c xs holds: each value counted at its
# last occurrence (no later piece holds it)
def kinds(xs: List<&2, Tk.Piece>, +c: Tk.Class) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> +rest:
      match x:
        case Tk.Plain{s}:
          kinds(rest, c)
        case Tk.Value{d, +w}:
          kinds.at(Bool.and(Sm.same_class(c, d), Bool.not(has(rest, c, w))), kinds(rest, c))

# the number of v among the values of class c in xs: one more than the
# distinct values of that class before its first occurrence
def number(+xs: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> Nat:
  1n+kinds(before(xs, c, v), c)

def numbered.of(r: Bool, +all: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> Tk.Seg:
  match r:
    case True{}:
      Tk.Tok{c, number(all, c, v)}
    case False{}:
      Tk.Hash{c, v}

# the text xs as it leaves a session whose texts so far, xs last, are all:
# plain text as it is, a value of a class that maps back as the token of
# its class with its number in all, a credential as its one-way token
def numbered(+all: List<&2, Tk.Piece>, xs: List<&2, Tk.Piece>) -> List<&2, Tk.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Txt{s} <> numbered(all, rest)
        case Tk.Value{+c, +v}:
          numbered.of(S.reversible(c), all, c, v) <> numbered(all, rest)

# Laws (R13)
# ----------

# LAW privacy_session_restores_own (R13): for every session (any texts
# xss, scrubbed in order from the empty map) and every answer ys, restoring
# ys against the session's map gives ys piece for piece, each piece kept,
# or a token of a class that maps back brought into clear as a value of
# that class one of the session's texts holds (a session with no texts
# holds none: it restores nothing). That a token the session issued does
# come back is privacy_round_trip_exact (every map, so every session's)
# EXCLUDES: a token restored to a value outside the session's own texts
#   (a map that opens holding values, as the daemon-wide map did for every
#   later session, or a table outside the map), a token restored to a
#   value of another class, a credential restored, a piece changed,
#   dropped or added
law privacy_session_restores_own:
  for +xss: List<&2, List<&2, Tk.Piece>>
  for +ys: List<&2, Tk.Seg>
  {all_came(history(xss), ys, Tk.restore(session(xss), ys)) == True{} : Bool}

# LAW privacy_session_numbers_from_one (R13): for every session (any texts
# xss, scrubbed in order from the empty map) and every next text xs, xs
# leaves with its plain text as it is, each credential as its one-way
# token, and each value of a class that maps back as the token of its class
# numbered by its place, from 1, among the distinct values of that class
# in the session's texts so far (xs last), in the order they first appear
# EXCLUDES: a session's first value of a class numbered past 1 (indexes
#   carried over from another session), one index space for every class,
#   a held value given a new number, a number that skips or repeats, a
#   value sent in clear, a credential mapped, plain text changed
law privacy_session_numbers_from_one:
  for +xss: List<&2, List<&2, Tk.Piece>>
  for +xs: List<&2, Tk.Piece>
  {Tk.Out.ys(Tk.scrub(session(xss), xs)) == numbered(List.append(&2, Tk.Piece, history(xss), xs), xs) : List<&2, Tk.Seg>}

# Anchors (R13)
# -------------

# session B's text: one IP address
def b_text() -> List<&2, Tk.Piece>:
  [Tk.Plain{"ping "}, Tk.Value{Tk.Ip{}, "10.0.0.2"}]

# LAW privacy_session_example (R13): anchor: the session that scrubbed
# 10.0.0.1 numbers 10.0.0.2 IP 2; a fresh session B numbers it IP 1, B's
# IP 1 restores B's address, and a session that scrubbed nothing leaves
# IP 1 a token
# EXCLUDES: the old daemon-wide map (B's address IP 2, B's IP 1 restored
#   to A's 10.0.0.1)
law privacy_session_example:
  {Tk.Out.ys(Tk.scrub(session([[Tk.Value{Tk.Ip{}, "10.0.0.1"}]]), b_text())) == [Tk.Txt{"ping "}, Tk.Tok{Tk.Ip{}, 2n}] : List<&2, Tk.Seg>} & {Tk.Out.ys(Tk.scrub(session([]), b_text())) == [Tk.Txt{"ping "}, Tk.Tok{Tk.Ip{}, 1n}] : List<&2, Tk.Seg>} & {Tk.restore(session([b_text()]), [Tk.Tok{Tk.Ip{}, 1n}]) == [Tk.Clear{Tk.Ip{}, "10.0.0.2"}] : List<&2, Tk.Seg>} & {Tk.restore(session([]), [Tk.Tok{Tk.Ip{}, 1n}]) == [Tk.Tok{Tk.Ip{}, 1n}] : List<&2, Tk.Seg>}
