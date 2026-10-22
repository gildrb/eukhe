# wire: the text format every entry of the compiled Bend core reads and
# writes (crates/eukhe-bend/WIRE.md is the grammar, with examples and the
# Rust Writer/Reader that mirrors this file). Pure: no IO, no @unsafe.
#
# Every value is self-delimiting, so values concatenate with no
# separator; a decoder knows the type it reads (no type tags):
#   Nat     canonical decimal, 1 to 14 digits, then ','     0,  42,
#   U32     a Nat <= 4294967295                             7,
#   Bool    T | F
#   String  its length in chars (a Nat), then the chars     5,héllo
#   List    its length (a Nat), then the items              2,1,2,
#   Maybe   0, (None) | 1, then the value (Some)            1,5,
#   a constructor: its tag (a Nat, declaration order), then its fields
#   a reply: the value, or the error form 'E ' + text      E bad input
#
# An encoder `put_x(x, rest)` answers the encoding of x followed by rest,
# so encoders compose with no append: put_nat(a, put_str(b, rest)). A
# decoder `get_x(s)` answers Got{x, rest} when s starts with an encoding
# of x, else Bad{}; it never folds more than 14 digits, so no input can
# push a Nat past the runtime's 2^48-1 bound. The laws (LAWS.bend section
# wire) pin both directions: get_x(put_x(x, rest)) == Got{x, rest}, and
# get_x(s) == Got{x, rest} only when s == put_x(x, rest).

import Base

# A decoder's answer: the value and the rest of the input, or malformed.
type Dec<-A: Data> is Data:
  Got{value: A, rest: String}
  Bad{}

# Digits
# ------

# A char that is a token of a Nat: a digit, the end mark ',' or another.
type Tok is Data:
  Dig{d: Nat}
  Comma{}
  Other{}

# The char of a digit (0..9); 10 and more never occur (put_nat's
# remainders are below 10).
def dchar(d: Nat) -> Char:
  match d:
    case 0n:
      '0'
    case 1n:
      '1'
    case 2n:
      '2'
    case 3n:
      '3'
    case 4n:
      '4'
    case 5n:
      '5'
    case 6n:
      '6'
    case 7n:
      '7'
    case 8n:
      '8'
    case 9n:
      '9'
    case 10n+p:
      '9'

# The codes of '0'..'9', in order.
def codes() -> List<&2, U32>:
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57]

def cdig.pick(hit: Bool, later: Maybe<&2, Nat>, i: Nat) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      later

# The digit whose code is x, the i-th of ds onwards.
def cdig.go(ds: List<&2, U32>, +x: U32, +i: Nat) -> Maybe<&2, Nat>:
  match ds:
    case Nil{}:
      None{}
    case Con{+h, t}:
      cdig.pick(U32.is_eq(x, h), cdig.go(t, x, 1n+i), i)

def tok.end(comma: Bool) -> Tok:
  match comma:
    case True{}:
      Comma{}
    case False{}:
      Other{}

def tok.of(m: Maybe<&2, Nat>, comma: Bool) -> Tok:
  match m:
    case Some{d}:
      Dig{d}
    case None{}:
      tok.end(comma)

# The token of a char.
def tok(c: Char) -> Tok:
  match c:
    case Chr{+x}:
      tok.of(cdig.go(codes(), x, 0n), U32.is_eq(x, 44))

# The token at the head of s and the rest (the end of input reads Other).
def peek(s: String) -> Tok & String:
  match s:
    case SNil{}:
      (Other{}, SNil{})
    case SCon{c, t}:
      (tok(c), t)

# Nat
# ---

# The digits of n before acc, most significant first; none when n is 0
# (the caller wrote the lowest digit). The fuel g bounds the digits
# (g >= n is enough).
def put_nat.go(g: Nat, n: Nat, acc: String) -> String:
  match g:
    case 0n:
      acc
    case 1n+f:
      match n:
        case 0n:
          acc
        case 1n+p:
          +m = {1n+p : Nat}
          put_nat.go(f, Nat.div(m, 10n), SCon{dchar(Nat.mod(m, 10n)), acc})

# The encoding of n, then rest.
def put_nat(n: Nat, rest: String) -> String:
  +m = n
  put_nat.go(m, Nat.div(m, 10n), SCon{dchar(Nat.mod(m, 10n)), SCon{',', rest}})

# The value of digits read last first: d0 + 10 * value(rest).
def value(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(d, Nat.mul(10n, value(t)))

# No digit is left: only the end mark may follow.
def get_nat.end(ts: Tok & String, ds: List<&2, Nat>) -> Dec<Nat>:
  (t, s) = ts
  match t:
    case Dig{d}:
      Bad{}
    case Comma{}:
      Got{value(ds), s}
    case Other{}:
      Bad{}

# Read at most k more digits after ds (read last first), then ','.
def get_nat.go(k: Nat, ts: Tok & String, ds: List<&2, Nat>) -> Dec<Nat>:
  match k:
    case 0n:
      get_nat.end(ts, ds)
    case 1n+j:
      (t, s) = ts
      match t:
        case Dig{d}:
          get_nat.go(j, peek(s), d <> ds)
        case Comma{}:
          Got{value(ds), s}
        case Other{}:
          Bad{}

def get_nat.lead(d: Nat, ts: Tok & String) -> Dec<Nat>:
  match d:
    case 0n:
      get_nat.end(ts, [0n])
    case 1n+p:
      get_nat.go(13n, ts, [1n+p])

# The first digit: 0 stands alone, any other starts up to 13 more.
def get_nat.first(ts: Tok & String) -> Dec<Nat>:
  (t, s) = ts
  match t:
    case Dig{d}:
      get_nat.lead(d, peek(s))
    case Comma{}:
      Bad{}
    case Other{}:
      Bad{}

def get_nat(s: String) -> Dec<Nat>:
  get_nat.first(peek(s))

# U32
# ---

def put_u32(x: U32, rest: String) -> String:
  put_nat(U32.to_nat(x), rest)

def get_u32.in(ok: Bool, x: U32, s: String) -> Dec<U32>:
  match ok:
    case True{}:
      Got{x, s}
    case False{}:
      Bad{}

# A Nat is a U32 when converting it to a U32 and back gives it again (no
# wrap): the test needs no constant 2^32.
def get_u32.fit(r: Dec<Nat>) -> Dec<U32>:
  match r:
    case Got{+n, s}:
      +x = U32.from_nat(n)
      get_u32.in(Nat.is_eq(U32.to_nat(x), n), x, s)
    case Bad{}:
      Bad{}

def get_u32(s: String) -> Dec<U32>:
  get_u32.fit(get_nat(s))

# Bool
# ----

def put_bool(b: Bool, rest: String) -> String:
  match b:
    case True{}:
      SCon{'T', rest}
    case False{}:
      SCon{'F', rest}

def get_bool.f(f: Bool, s: String) -> Dec<Bool>:
  match f:
    case True{}:
      Got{False{}, s}
    case False{}:
      Bad{}

def get_bool.pick(t: Bool, f: Bool, s: String) -> Dec<Bool>:
  match t:
    case True{}:
      Got{True{}, s}
    case False{}:
      get_bool.f(f, s)

def get_bool(s: String) -> Dec<Bool>:
  match s:
    case SNil{}:
      Bad{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          get_bool.pick(U32.is_eq(x, 84), U32.is_eq(x, 70), t)

# String
# ------

def put_str.step(c: Char, r: Nat & String) -> Nat & String:
  (n, s) = r
  (1n+n, SCon{c, s})

# The chars of a, then rest, and how many there are.
def put_str.go(a: String, rest: String) -> Nat & String:
  match a:
    case SNil{}:
      (0n, rest)
    case SCon{c, t}:
      put_str.step(c, put_str.go(t, rest))

def put_str.fin(r: Nat & String) -> String:
  (n, s) = r
  put_nat(n, s)

def put_str(a: String, rest: String) -> String:
  put_str.fin(put_str.go(a, rest))

def take.cons(c: Char, r: Dec<String>) -> Dec<String>:
  match r:
    case Got{a, s}:
      Got{SCon{c, a}, s}
    case Bad{}:
      Bad{}

# The first n chars of s and the rest.
def take(n: Nat, s: String) -> Dec<String>:
  match n:
    case 0n:
      Got{SNil{}, s}
    case 1n+m:
      match s:
        case SNil{}:
          Bad{}
        case SCon{c, t}:
          take.cons(c, take(m, t))

def get_str.go(r: Dec<Nat>) -> Dec<String>:
  match r:
    case Got{n, s}:
      take(n, s)
    case Bad{}:
      Bad{}

def get_str(s: String) -> Dec<String>:
  get_str.go(get_nat(s))

# Lists (templates over the item's codec)
# -----

def put_list.step(~A: Data, ~put: A -> String -> String, x: A, r: Nat & String) -> Nat & String:
  (n, s) = r
  (1n+n, put(x, s))

# The items of xs, then rest, and how many there are.
def put_list.go(~A: Data, ~put: A -> String -> String, xs: List<&2, A>, rest: String) -> Nat & String:
  match xs:
    case Nil{}:
      (0n, rest)
    case Con{x, t}:
      put_list.step(~A, ~put, x, put_list.go(~A, ~put, t, rest))

def put_list.fin(r: Nat & String) -> String:
  (n, s) = r
  put_nat(n, s)

def put_list(~A: Data, ~put: A -> String -> String, xs: List<&2, A>, rest: String) -> String:
  put_list.fin(put_list.go(~A, ~put, xs, rest))

def get_list.cons(-A: Data, x: A, r: Dec<List<&2, A>>) -> Dec<List<&2, A>>:
  match r:
    case Got{xs, s}:
      Got{x <> xs, s}
    case Bad{}:
      Bad{}

# n more items after the one cur answers (cur: the decoder's answer at it).
def get_list.go(~A: Data, ~get: String -> Dec<A>, n: Nat, cur: Dec<A>) -> Dec<List<&2, A>>:
  match n:
    case 0n:
      match cur:
        case Got{x, s}:
          Got{[x], s}
        case Bad{}:
          Bad{}
    case 1n+m:
      match cur:
        case Got{x, s}:
          get_list.cons(A, x, get_list.go(~A, ~get, m, get(s)))
        case Bad{}:
          Bad{}

def get_list.start(~A: Data, ~get: String -> Dec<A>, r: Dec<Nat>) -> Dec<List<&2, A>>:
  match r:
    case Got{n, s}:
      match n:
        case 0n:
          Got{Nil{}, s}
        case 1n+m:
          get_list.go(~A, ~get, m, get(s))
    case Bad{}:
      Bad{}

def get_list(~A: Data, ~get: String -> Dec<A>, s: String) -> Dec<List<&2, A>>:
  get_list.start(~A, ~get, get_nat(s))

# Replies
# -------

# The error form of a reply.
def err(text: String) -> String:
  SCon{'E', SCon{' ', text}}

# Nothing is left of the input.
def end(s: String) -> Bool:
  String.is_empty(s)
