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
