# privacy/token: the tokens of the outbound scrubber
# (crates/eukhe-ai/src/privacy), as the compiled core runs them
# (bend/ffi_privacy.bend's stepper; Rust: eukhe-bend rules/privacy.rs,
# held by eukhe-ai privacy/mod.rs for the daemon's life).
# laws/privacy/token.bend pins it against spec/harness/privacy.bend.
#
# 1. Classes. Personal values (PERSON, EMAIL, PHONE, IP, ID) map back:
#    their token is CLASS_<n>, one index space per class, from 1.
#    Credentials (KEY, CARD, IBAN) go one way: their token is a hash Rust
#    writes (CLASS_<6 hex of the value's SHA-256>), never mapped back.
# 2. The map. Append-only: a value keeps its index for the map's life; a
#    new value of a class takes the next index of that class.
# 3. A text. The scrubber reads a text as plain pieces and values (a
#    literal that reads as a token is itself a value of its class), and
#    asks for the tokens of its values, in order, in one step. The restore
#    reads a text as plain text and tokens, and asks for the values of its
#    tokens, in one step: a mapped token the map holds comes back as its
#    value; every other token stays.
# 4. A failover. Every attempt of a request (the primary and each sibling)
#    sends the raw context: scrubbed when its model is remote, as it is
#    when its model is local. No attempt reads another's text.

import Base

# Classes
# -------

type Class is Data:
  Person{}
  Email{}
  Phone{}
  Ip{}
  Id{}
  ApiKey{}
  Card{}
  Iban{}

# the wire tag of a class (crates/eukhe-bend/src/rules/privacy.rs)
def Class.tag(c: Class) -> Nat:
  match c:
    case Person{}:
      0n
    case Email{}:
      1n
    case Phone{}:
      2n
    case Ip{}:
      3n
    case Id{}:
      4n
    case ApiKey{}:
      5n
    case Card{}:
      6n
    case Iban{}:
      7n

def Class.of(n: Nat) -> Maybe<&2, Class>:
  match n:
    case 0n:
      Some{Person{}}
    case 1n:
      Some{Email{}}
    case 2n:
      Some{Phone{}}
    case 3n:
      Some{Ip{}}
    case 4n:
      Some{Id{}}
    case 5n:
      Some{ApiKey{}}
    case 6n:
      Some{Card{}}
    case 7n:
      Some{Iban{}}
    case 8n+p:
      None{}

def Class.eq(a: Class, b: Class) -> Bool:
  Nat.is_eq(Class.tag(a), Class.tag(b))

# a token of the class maps back to its value
def reversible(c: Class) -> Bool:
  match c:
    case Person{}:
      True{}
    case Email{}:
      True{}
    case Phone{}:
      True{}
    case Ip{}:
      True{}
    case Id{}:
      True{}
    case ApiKey{}:
      False{}
    case Card{}:
      False{}
    case Iban{}:
      False{}

def mapped.keep(b: Bool, +c: Class, rest: List<&2, Class>) -> List<&2, Class>:
  match b:
    case True{}:
      c <> rest
    case False{}:
      rest

# the classes of cs whose tokens map back, in order
def mapped.go(cs: List<&2, Class>) -> List<&2, Class>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      mapped.keep(reversible(c), c, mapped.go(rest))

# the classes whose tokens map back (reversible), in tag order: the one
# list Rust reads literal tokens of
def mapped_classes() -> List<&2, Class>:
  mapped.go([Person{}, Email{}, Phone{}, Ip{}, Id{}, ApiKey{}, Card{}, Iban{}])

# The book
# --------

# a value of a class
type Ent is Data:
  Ent{c: Class, v: String}

# the map: the values mapped, newest first
type Book is Data:
  Book{es: List<&2, Ent>}

def Book.empty() -> Book:
  Book{Nil{}}

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# how many values of class c es holds
def count(es: List<&2, Ent>, +c: Class) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Ent{d, w}:
          Nat.add(bit(Class.eq(c, d)), count(rest, c))

# a and b are the same text, char by char
def same(a: String, b: String) -> Bool:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          True{}
        case SCon{y, bt}:
          False{}
    case SCon{x, at}:
      match b:
        case SNil{}:
          False{}
        case SCon{y, bt}:
          Bool.and(Char.is_eq(x, y), same(at, bt))

def find.at(hit: Bool, +es: List<&2, Ent>, +c: Class, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{1n+count(es, c)}
    case False{}:
      m

# the index of v in class c: 1 + the values of class c mapped before it
def find(es: List<&2, Ent>, +c: Class, +v: String) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case e <> +rest:
      match e:
        case Ent{d, w}:
          find.at(Bool.and(Class.eq(c, d), same(v, w)), rest, c, find(rest, c, v))

def value.at(hit: Bool, +w: String, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{w}
    case False{}:
      m

# the value of class c at index i
def value(es: List<&2, Ent>, +c: Class, +i: Nat) -> Maybe<&2, String>:
  match es:
    case Nil{}:
      None{}
    case e <> +rest:
      match e:
        case Ent{d, +w}:
          value.at(Bool.and(Class.eq(c, d), Nat.is_eq(i, 1n+count(rest, c))), w, value(rest, c, i))

# Tokens
# ------

# the token of a value: its index (a value that maps back), or one way
type Tok is Data:
  Mapped{i: Nat}
  OneWay{}

# a token, and the map after it
type Step is Data:
  Step{m: Book, t: Tok}

def Step.m(r: Step) -> Book:
  match r:
    case Step{m, t}:
      m

def Step.t(r: Step) -> Tok:
  match r:
    case Step{m, t}:
      t

def Book.es(m: Book) -> List<&2, Ent>:
  match m:
    case Book{es}:
      es

def scrub_val.new(+es: List<&2, Ent>, +c: Class, +v: String, f: Maybe<&2, Nat>) -> Step:
  match f:
    case Some{i}:
      Step{Book{es}, Mapped{i}}
    case None{}:
      Step{Book{Ent{c, v} <> es}, Mapped{1n+count(es, c)}}

def scrub_val.of(r: Bool, +m: Book, +c: Class, +v: String) -> Step:
  match r:
    case True{}:
      scrub_val.new(Book.es(m), c, v, find(Book.es(m), c, v))
    case False{}:
      Step{m, OneWay{}}

# the token of v in class c, and the map after it
def scrub_val(+m: Book, +c: Class, +v: String) -> Step:
  scrub_val.of(reversible(c), m, c, v)

# a value to scrub: its class and its text
type Val is Data:
  Val{c: Class, v: String}

# tokens, and the map after them
type Toks is Data:
  Toks{m: Book, ts: List<&2, Tok>}

def Toks.m(r: Toks) -> Book:
  match r:
    case Toks{m, ts}:
      m

def Toks.ts(r: Toks) -> List<&2, Tok>:
  match r:
    case Toks{m, ts}:
      ts

def scrub_vals.cons(t: Tok, r: Toks) -> Toks:
  match r:
    case Toks{m, ts}:
      Toks{m, t <> ts}

# the tokens of the values of one text, in order, and the map after them
def scrub_vals(vs: List<&2, Val>, m: Book) -> Toks:
  match vs:
    case Nil{}:
      Toks{m, Nil{}}
    case x <> rest:
      match x:
        case Val{c, v}:
          +r = scrub_val(m, c, v)
          scrub_vals.cons(Step.t(r), scrub_vals(rest, Step.m(r)))

def restore_tok.of(r: Bool, +m: Book, +c: Class, +i: Nat) -> Maybe<&2, String>:
  match r:
    case True{}:
      value(Book.es(m), c, i)
    case False{}:
      None{}

# the value of the token of class c and index i: none for a token the map
# does not hold, and for every one-way class
def restore_tok(+m: Book, +c: Class, +i: Nat) -> Maybe<&2, String>:
  restore_tok.of(reversible(c), m, c, i)

# a token to restore: its class and index
type Ref is Data:
  Ref{c: Class, i: Nat}

# the values of the tokens of one text, in order
def restore_toks(rs: List<&2, Ref>, +m: Book) -> List<&2, Maybe<&2, String>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Ref{c, i}:
          restore_tok(m, c, i) <> restore_toks(rest, m)

# Texts
# -----

# a text as the scrubber reads it
type Piece is Data:
  Plain{s: String}
  Value{c: Class, v: String}

# a text as it leaves, or as the model answers: plain text, a value, a
# mapped token, a one-way token (of the value it hides)
type Seg is Data:
  Txt{s: String}
  Clear{c: Class, v: String}
  Tok{c: Class, i: Nat}
  Hash{c: Class, v: String}

# the values of a text, in order
def vals(xs: List<&2, Piece>) -> List<&2, Val>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Plain{s}:
          vals(rest)
        case Value{c, v}:
          Val{c, v} <> vals(rest)

# the text with each value replaced by its token, in order
def fill(xs: List<&2, Piece>, ts: List<&2, Tok>) -> List<&2, Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Plain{s}:
          Txt{s} <> fill(rest, ts)
        case Value{c, v}:
          match ts:
            case Nil{}:
              Clear{c, v} <> fill(rest, Nil{})
            case t <> more:
              match t:
                case Mapped{i}:
                  Tok{c, i} <> fill(rest, more)
                case OneWay{}:
                  Hash{c, v} <> fill(rest, more)

# a text, and the map after it
type Out is Data:
  Out{m: Book, ys: List<&2, Seg>}

def Out.m(r: Out) -> Book:
  match r:
    case Out{m, ys}:
      m

def Out.ys(r: Out) -> List<&2, Seg>:
  match r:
    case Out{m, ys}:
      ys

def scrub.fill(+xs: List<&2, Piece>, r: Toks) -> Out:
  match r:
    case Toks{m, ts}:
      Out{m, fill(xs, ts)}

# a text scrubbed: one step for its values, each replaced by its token
def scrub(m: Book, +xs: List<&2, Piece>) -> Out:
  scrub.fill(xs, scrub_vals(vals(xs), m))

# the tokens of a text, in order
def refs(ys: List<&2, Seg>) -> List<&2, Ref>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> rest:
      match y:
        case Txt{s}:
          refs(rest)
        case Clear{c, v}:
          refs(rest)
        case Tok{c, i}:
          Ref{c, i} <> refs(rest)
        case Hash{c, v}:
          refs(rest)

# the text with each token that has a value replaced by it, in order
def back(ys: List<&2, Seg>, fs: List<&2, Maybe<&2, String>>) -> List<&2, Seg>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> rest:
      match y:
        case Txt{s}:
          Txt{s} <> back(rest, fs)
        case Clear{c, v}:
          Clear{c, v} <> back(rest, fs)
        case Hash{c, v}:
          Hash{c, v} <> back(rest, fs)
        case Tok{c, i}:
          match fs:
            case Nil{}:
              Tok{c, i} <> back(rest, Nil{})
            case f <> more:
              match f:
                case None{}:
                  Tok{c, i} <> back(rest, more)
                case Some{v}:
                  Clear{c, v} <> back(rest, more)

# a text restored: one step for its tokens, each that has a value
# replaced by it
def restore(+m: Book, +ys: List<&2, Seg>) -> List<&2, Seg>:
  back(ys, restore_toks(refs(ys), m))

# Failover
# --------

# the raw text, as a local model reads it
def raw(xs: List<&2, Piece>) -> List<&2, Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Plain{s}:
          Txt{s} <> raw(rest)
        case Value{c, v}:
          Clear{c, v} <> raw(rest)

# the texts of the attempts, and the map after them
type Sent is Data:
  Sent{m: Book, yss: List<&2, List<&2, Seg>>}

def Sent.yss(r: Sent) -> List<&2, List<&2, Seg>>:
  match r:
    case Sent{m, yss}:
      yss

def send.cons(y: List<&2, Seg>, r: Sent) -> Sent:
  match r:
    case Sent{m, ys}:
      Sent{m, y <> ys}

# the texts the attempts of one request send, one per attempt (True: its
# model is remote), each from the raw text xs, and the map after them
def send(ts: List<&2, Bool>, m: Book, +xs: List<&2, Piece>) -> Sent:
  match ts:
    case Nil{}:
      Sent{m, Nil{}}
    case t <> rest:
      match t:
        case True{}:
          +r = scrub(m, xs)
          send.cons(Out.ys(r), send(rest, Out.m(r), xs))
        case False{}:
          send.cons(raw(xs), send(rest, m, xs))
