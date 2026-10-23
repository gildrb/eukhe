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
# push a Nat past the runtime's 2^48-1 bound. The laws (laws/wire.bend)
# pin both directions: get_x(put_x(x, rest)) == Got{x, rest}, and
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

def tok.end(comma: Bool) -> Tok:
  match comma:
    case True{}:
      Comma{}
    case False{}:
      Other{}

def tok.is(ok: Bool, d: Nat, comma: Bool) -> Tok:
  match ok:
    case True{}:
      Dig{d}
    case False{}:
      tok.end(comma)

# The token of the char of code x, where d is its code less 48 (0 below
# 48): a digit when d is below 10 and x is the code of d again.
def tok.code(+x: U32, +d: Nat) -> Tok:
  tok.is(Bool.and(Nat.is_lt(d, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d)))), d, U32.is_eq(x, 44))

# The token of a char: native compares on its code, no table.
def tok(c: Char) -> Tok:
  match c:
    case Chr{+x}:
      tok.code(x, Nat.sub(U32.to_nat(x), 48n))

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

# No digit is left: only the end mark may follow (t is the token of the
# char before s).
def get_nat.end(t: Tok, s: String, v: Nat) -> Dec<Nat>:
  match t:
    case Dig{d}:
      Bad{}
    case Comma{}:
      Got{v, s}
    case Other{}:
      Bad{}

# Read at most k more digits after those worth v, then ','; t is the
# token of the char before s. One flat loop: the value folds as it reads
# (v * 10 + d), and k counts the digits, so at most 14 are ever folded.
def get_nat.go(k: Nat, t: Tok, s: String, v: Nat) -> Dec<Nat>:
  match k:
    case 0n:
      get_nat.end(t, s, v)
    case 1n+j:
      match t:
        case Dig{d}:
          match s:
            case SNil{}:
              Bad{}
            case SCon{c, r}:
              get_nat.go(j, tok(c), r, Nat.add(d, Nat.mul(10n, v)))
        case Comma{}:
          Got{v, s}
        case Other{}:
          Bad{}

def get_nat.lead(d: Nat, t: Tok, s: String) -> Dec<Nat>:
  match d:
    case 0n:
      get_nat.end(t, s, 0n)
    case 1n+p:
      get_nat.go(13n, t, s, 1n+p)

# The first digit: 0 stands alone, any other starts up to 13 more.
def get_nat.first(t: Tok, s: String) -> Dec<Nat>:
  match t:
    case Dig{d}:
      match s:
        case SNil{}:
          Bad{}
        case SCon{c, r}:
          get_nat.lead(d, tok(c), r)
    case Comma{}:
      Bad{}
    case Other{}:
      Bad{}

def get_nat(s: String) -> Dec<Nat>:
  match s:
    case SNil{}:
      Bad{}
    case SCon{c, r}:
      get_nat.first(tok(c), r)

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

# The chars of a reversed onto acc, and n plus how many there are (one
# flat loop).
def put_str.go(a: String, acc: String, n: Nat) -> Nat & String:
  match a:
    case SNil{}:
      (n, acc)
    case SCon{c, t}:
      put_str.go(t, SCon{c, acc}, 1n+n)

def put_str.fin(r: Nat & String, rest: String) -> String:
  (n, b) = r
  put_nat(n, String.reverse.go(b, rest))

def put_str(a: String, rest: String) -> String:
  put_str.fin(put_str.go(a, SNil{}, 0n), rest)

# The first n chars of s, reversed onto acc, and the rest (one flat loop;
# the chars are turned around once at the end).
def take.go(n: Nat, s: String, acc: String) -> Dec<String>:
  match n:
    case 0n:
      Got{String.reverse(acc), s}
    case 1n+m:
      match s:
        case SNil{}:
          Bad{}
        case SCon{c, t}:
          take.go(m, t, SCon{c, acc})

# The first n chars of s and the rest.
def take(n: Nat, s: String) -> Dec<String>:
  take.go(n, s, SNil{})

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
