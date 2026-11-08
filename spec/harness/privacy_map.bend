# privacy (spec): the token map of the outbound scrubber (spec/README.md
# H7; the stepper of bend/ffi_privacy.bend, held by eukhe-ai
# privacy/mod.rs for the daemon's life), restated without the code
# (bend/privacy/token.bend's count, find and value): a state machine over
# the values each class holds. A spec: the shipped code never calls it (it
# uses the code's data types only: the map is a Tk.Book, its values newest
# first).
#
# M1: the map holds, for each class, the values given a token, in the
#     order they were first scrubbed (read oldest first).
# M2: a value of a class that maps back (S4) takes the token of its place
#     among its class's values, from 1: a value its class holds keeps its
#     place and the map stays; a new one joins its class last and takes
#     the next place. A value of a one-way class takes the one-way token
#     and the map stays. The values of a text take their tokens in order,
#     each from the map the one before it left.
# M3: a token of a class that maps back restores the value at its place
#     among its class's values, when the class holds one there; a token of
#     a one-way class, or of a place its class does not hold, restores
#     nothing. A restore leaves the map as it was.
# M4: the map opens empty, and no class ever holds a value twice (M2 adds
#     only a value its class does not hold).
# M5: a text (the pieces Rust reads: plain text and values) is scrubbed in
#     one step: its values, in order, take their tokens (M2), and the text
#     leaves with each value replaced by its token: a mapped token as its
#     class and place, a one-way token as the token of the value it hides.
#     A text restored is the text with each token replaced by the value
#     M3 restores for it, when there is one. Every attempt of a failover
#     sends from the raw text: a remote one the text scrubbed from the map
#     the attempts before it left, a local one the text itself.

import Base
import ../../bend/privacy/token.bend as Tk
import ./privacy.bend as S

# Classes
# -------

# a number per class, to tell classes apart
def ord(c: Tk.Class) -> Nat:
  match c:
    case Tk.Person{}:
      0n
    case Tk.Email{}:
      1n
    case Tk.Phone{}:
      2n
    case Tk.Ip{}:
      3n
    case Tk.Id{}:
      4n
    case Tk.ApiKey{}:
      5n
    case Tk.Card{}:
      6n
    case Tk.Iban{}:
      7n

def same_class(a: Tk.Class, b: Tk.Class) -> Bool:
  Nat.is_eq(ord(a), ord(b))

# M1: what a class holds
# ----------------------

def held.add(hit: Bool, xs: List<&2, String>, +w: String) -> List<&2, String>:
  match hit:
    case True{}:
      List.append(&2, String, xs, [w])
    case False{}:
      xs

# the values of class c the map es (newest first) holds, oldest first
def held(es: List<&2, Tk.Ent>, +c: Tk.Class) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Tk.Ent{d, w}:
          held.add(same_class(c, d), held(rest, c), w)

def place.later(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{1n+i}

def place.at(hit: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{1n}
    case False{}:
      place.later(m)

# the place of v among xs, from 1: its first
def place(xs: List<&2, String>, +v: String) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> rest:
      place.at(String.eq(v, x), place(rest, v))

# the value at place i of xs, from 1
def at(xs: List<&2, String>, i: Nat) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case x <> rest:
      match i:
        case 0n:
          None{}
        case 1n+j:
          match j:
            case 0n:
              Some{x}
            case 1n+k:
              at(rest, j)

def fresh(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{i}:
      False{}

# M4: no class holds a value twice: each value is new to its class among
# the values mapped before it
def distinct(es: List<&2, Tk.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> +rest:
      match e:
        case Tk.Ent{+d, +w}:
          Bool.and(fresh(place(held(rest, d), w)), distinct(rest))

def book_distinct(b: Tk.Book) -> Bool:
  match b:
    case Tk.Book{es}:
      distinct(es)

# M2: a scrub
# -----------

def scrub1.place(m: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String) -> Tk.Step:
  match m:
    case Some{i}:
      Tk.Step{Tk.Book{es}, Tk.Mapped{i}}
    case None{}:
      Tk.Step{Tk.Book{Tk.Ent{c, v} <> es}, Tk.Mapped{1n+List.length(&2, String, held(es, c))}}

def scrub1.of(back: Bool, b: Tk.Book, +c: Tk.Class, +v: String) -> Tk.Step:
  match back:
    case True{}:
      match b:
        case Tk.Book{+es}:
          scrub1.place(place(held(es, c), v), es, c, v)
    case False{}:
      Tk.Step{b, Tk.OneWay{}}

# the token of value v of class c, and the map after it
def scrub1(b: Tk.Book, +c: Tk.Class, +v: String) -> Tk.Step:
  scrub1.of(S.reversible(c), b, c, v)

def step_book(r: Tk.Step) -> Tk.Book:
  match r:
    case Tk.Step{m, t}:
      m

def step_tok(r: Tk.Step) -> Tk.Tok:
  match r:
    case Tk.Step{m, t}:
      t

def push(t: Tk.Tok, r: Tk.Toks) -> Tk.Toks:
  match r:
    case Tk.Toks{m, ts}:
      Tk.Toks{m, t <> ts}

# the tokens of the values of a text, in order, and the map after them
def scrub_vals(vs: List<&2, Tk.Val>, b: Tk.Book) -> Tk.Toks:
  match vs:
    case Nil{}:
      Tk.Toks{b, Nil{}}
    case x <> rest:
      match x:
        case Tk.Val{c, v}:
          +r = scrub1(b, c, v)
          push(step_tok(r), scrub_vals(rest, step_book(r)))

def toks_book(r: Tk.Toks) -> Tk.Book:
  match r:
    case Tk.Toks{m, ts}:
      m

# M3: a restore
# -------------

def restore1.of(back: Bool, b: Tk.Book, +c: Tk.Class, +i: Nat) -> Maybe<&2, String>:
  match back:
    case True{}:
      match b:
        case Tk.Book{es}:
          at(held(es, c), i)
    case False{}:
      None{}

# the value of the token of class c and place i
def restore1(b: Tk.Book, +c: Tk.Class, +i: Nat) -> Maybe<&2, String>:
  restore1.of(S.reversible(c), b, c, i)

# the values of the tokens of a text, in order
def restore_toks(rs: List<&2, Tk.Ref>, +b: Tk.Book) -> List<&2, Maybe<&2, String>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Tk.Ref{c, i}:
          restore1(b, c, i) <> restore_toks(rest, b)

# M5: a text
# ----------

# the values of a text, in order
def vals(xs: List<&2, Tk.Piece>) -> List<&2, Tk.Val>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          vals(rest)
        case Tk.Value{c, v}:
          Tk.Val{c, v} <> vals(rest)

# a value as it leaves: its class and place, or the one-way token of it
def seg(+c: Tk.Class, +v: String, t: Tk.Tok) -> Tk.Seg:
  match t:
    case Tk.Mapped{i}:
      Tk.Tok{c, i}
    case Tk.OneWay{}:
      Tk.Hash{c, v}

# a text with its values replaced by the tokens ts, in order (one token
# per value; a value past the last token stays as it is)
def fill(xs: List<&2, Tk.Piece>, ts: List<&2, Tk.Tok>) -> List<&2, Tk.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          Tk.Txt{s} <> fill(rest, ts)
        case Tk.Value{+c, +v}:
          match ts:
            case Nil{}:
              Tk.Clear{c, v} <> fill(rest, Nil{})
            case t <> more:
              seg(c, v, t) <> fill(rest, more)

# a text as it leaves with the tokens r of its values, and the map after
# them
def text(+xs: List<&2, Tk.Piece>, r: Tk.Toks) -> Tk.Out:
  match r:
    case Tk.Toks{m, ts}:
      Tk.Out{m, fill(xs, ts)}

# a text scrubbed from map b: its values take their tokens in one step
def scrub_text(+xs: List<&2, Tk.Piece>, b: Tk.Book) -> Tk.Out:
  text(xs, scrub_vals(vals(xs), b))

def out_book(r: Tk.Out) -> Tk.Book:
  match r:
    case Tk.Out{m, ys}:
      m

def out_ys(r: Tk.Out) -> List<&2, Tk.Seg>:
  match r:
    case Tk.Out{m, ys}:
      ys

def restore_seg.tok(+c: Tk.Class, +i: Nat, f: Maybe<&2, String>) -> Tk.Seg:
  match f:
    case None{}:
      Tk.Tok{c, i}
    case Some{v}:
      Tk.Clear{c, v}

# a piece restored: a token by its value (M3), when there is one
def restore_seg(+b: Tk.Book, y: Tk.Seg) -> Tk.Seg:
  match y:
    case Tk.Txt{s}:
      Tk.Txt{s}
    case Tk.Clear{c, v}:
      Tk.Clear{c, v}
    case Tk.Tok{+c, +i}:
      restore_seg.tok(c, i, restore1(b, c, i))
    case Tk.Hash{c, v}:
      Tk.Hash{c, v}

# a text restored against map b, piece by piece
def restore_text(ys: List<&2, Tk.Seg>, +b: Tk.Book) -> List<&2, Tk.Seg>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> rest:
      restore_seg(b, y) <> restore_text(rest, b)

def send.cons(y: List<&2, Tk.Seg>, r: Tk.Sent) -> Tk.Sent:
  match r:
    case Tk.Sent{m, yss}:
      Tk.Sent{m, y <> yss}

# the texts the attempts of one request send (True: a remote model), each
# from the raw text xs, and the map after them
def send(ts: List<&2, Bool>, b: Tk.Book, +xs: List<&2, Tk.Piece>) -> Tk.Sent:
  match ts:
    case Nil{}:
      Tk.Sent{b, Nil{}}
    case t <> rest:
      match t:
        case True{}:
          +r = scrub_text(xs, b)
          send.cons(out_ys(r), send(rest, out_book(r), xs))
        case False{}:
          send.cons(S.raw(xs), send(rest, b, xs))
