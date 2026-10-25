# redirect_input: the pasted authorization input of the localhost-callback
# logins (Rust: eukhe-bend rules/redirect_input.rs; asked by eukhe-core
# auth/redirect_input.rs): the cleaned paste, the code and state it
# carries, the state check, and the user-facing texts of the paste loop.
#
# Clean: whitespace (Rust `char::is_whitespace`, gateway_answer's `space`)
# and the zero-width chars U+200B, U+200C, U+200D, U+2060, U+FEFF dropped
# anywhere, then the wrapping chars `"` `'` `` ` `` `<` `>` U+201C U+201D
# U+2018 U+2019 trimmed at both ends.
#
# Parse (the cleaned text): with a `?`, the query after the first `?` up to
# its first `#` (trailing `/`s dropped), then the fragment after that `#`;
# else with a `://`, the fragment after the first `#` after it; else the
# head before the first `#` and the fragment after it: a head that holds a
# `code=`, `state=` or `error=` pair (key before the pair's first `=`,
# pairs split at `&`) is the query (trailing `/`s dropped), else such a
# fragment, else an empty head has no code, else the head is the code and a
# non-empty fragment the state.
#
# The parameters of carriers (in order): Rust's form_urlencoded::parse:
# pairs split at `&`, empty ones skipped, the name before the first `=`
# and the value after it (none: empty); both decoded (`+` is a space, `%`
# and two hex digits a byte, then the bytes read as UTF-8 with each
# maximal invalid part one U+FFFD). A name's value: the first carrier with
# a pair of that name and a non-empty value, its first such pair. An
# `error` wins (with its `error_description`), then a `code` (with its
# `state`), else no code.
# Pure: no IO, no @unsafe.

import Base
import ./gateway_answer.bend as Ga

# Why a paste cannot complete the login
type Fail is Data:
  FMissing{}
  FMismatch{}
  FProvider{error: String, description: Maybe<&2, String>}

# A paste's code and state, or why it fails
type Answer is Data:
  Pasted{code: String, state: Maybe<&2, String>}
  Failed{fail: Fail}

# Clean
# -----

def zero_width(c: Char) -> Bool:
  Ga.in(Char.to_u32(c), [8203, 8204, 8205, 8288, 65279])

def wrapper(c: Char) -> Bool:
  Ga.in(Char.to_u32(c), [34, 39, 96, 60, 62, 8220, 8221, 8216, 8217])

def compact.at(drop: Bool, c: Char, r: String) -> String:
  match drop:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# s without whitespace and zero-width chars
def compact(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      compact.at(Bool.or(Ga.space(c), zero_width(c)), c, compact(t))

def unwrap.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading wrapping chars
def unwrap(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      unwrap.at(wrapper(c), c, t, unwrap(t))

# the paste as typed: compacted, then wrapping chars trimmed at both ends
def clean(s: String) -> String:
  String.reverse(unwrap(String.reverse(unwrap(compact(s)))))

# Text
# ----

# Text before a char, and the text after it
type Cut is Data:
  Cut{head: String, tail: String}

def split.at(b: Bool, c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match b:
    case True{}:
      Some{Cut{SNil{}, t}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Cut{h, u}:
              Some{Cut{SCon{c, h}, u}}

# s split at its first `sep` (none without one)
def split(s: String, +sep: Char) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      split.at(Char.is_eq(c, sep), c, t, split(t, sep))

def scheme.at(b: Bool, t: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{String.drop(t, 2n)}
    case False{}:
      r

# the text after the first `://` (none without one)
def scheme(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      scheme.at(String.starts_with(SCon{c, t}, "://"), t, scheme(t))

def slashes.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def slashes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      slashes.at(Char.is_eq(c, '/'), c, t, slashes(t))

# s without its trailing `/`s
def unslash(s: String) -> String:
  String.reverse(slashes(String.reverse(s)))

# the text after the first `#` (empty without one)
def fragment(m: Maybe<&2, Cut>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{x}:
      match x:
        case Cut{h, u}:
          u

# Decoding
# --------

# A unit of a decoded text: a char of the text, or a byte of a `%XX`
type Piece is Data:
  UChar{c: Char}
  UByte{b: U32}

def hexv.at(dec: Bool, low: Bool, up: Bool, +x: U32) -> Maybe<&2, U32>:
  match dec:
    case True{}:
      Some{U32.sub(x, 48)}
    case False{}:
      match low:
        case True{}:
          Some{U32.sub(x, 87)}
        case False{}:
          match up:
            case True{}:
              Some{U32.sub(x, 55)}
            case False{}:
              None{}

def within(+x: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# the value of an ASCII hex digit
def hexv(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      hexv.at(within(x, 48, 57), within(x, 97, 102), within(x, 65, 70), x)

# The percent reader's state: plain text, after a `%`, after `%` and a hex
# digit
type Pct is Data:
  PPlain{}
  PSign{}
  PDigit{h: Char, v: U32}

# What a char in plain text adds: `%` nothing yet, `+` a space
def plain.out(pct: Bool, plus: Bool, c: Char) -> List<&2, Piece>:
  match pct:
    case True{}:
      []
    case False{}:
      match plus:
        case True{}:
          [UChar{' '}]
        case False{}:
          [UChar{c}]

def plain.next(pct: Bool) -> Pct:
  match pct:
    case True{}:
      PSign{}
    case False{}:
      PPlain{}

def sign.out(m: Maybe<&2, U32>, +c: Char) -> List<&2, Piece>:
  match m:
    case None{}:
      UChar{'%'} <> plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Some{v}:
      []

def sign.next(m: Maybe<&2, U32>, +c: Char) -> Pct:
  match m:
    case None{}:
      plain.next(Char.is_eq(c, '%'))
    case Some{v}:
      PDigit{c, v}

def digit.out(m: Maybe<&2, U32>, h: Char, v: U32, +c: Char) -> List<&2, Piece>:
  match m:
    case None{}:
      UChar{'%'} <> UChar{h} <> plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Some{w}:
      [UByte{U32.add(U32.mul(v, 16), w)}]

def digit.next(m: Maybe<&2, U32>, +c: Char) -> Pct:
  match m:
    case None{}:
      plain.next(Char.is_eq(c, '%'))
    case Some{w}:
      PPlain{}

# what a char adds in a state: a `%` not followed by two hex digits is a
# char, the chars after it read again as plain text
def pout(st: Pct, +c: Char) -> List<&2, Piece>:
  match st:
    case PPlain{}:
      plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case PSign{}:
      sign.out(hexv(c), c)
    case PDigit{h, v}:
      digit.out(hexv(c), h, v, c)

# the state after a char
def pnext(st: Pct, +c: Char) -> Pct:
  match st:
    case PPlain{}:
      plain.next(Char.is_eq(c, '%'))
    case PSign{}:
      sign.next(hexv(c), c)
    case PDigit{h, v}:
      digit.next(hexv(c), c)

def pend(st: Pct) -> List<&2, Piece>:
  match st:
    case PPlain{}:
      []
    case PSign{}:
      [UChar{'%'}]
    case PDigit{h, v}:
      [UChar{'%'}, UChar{h}]

# the pieces of a text from a state: `+` a space, `%` and two hex digits a
# byte, any other `%` a char
def units(s: String, +st: Pct) -> List<&2, Piece>:
  match s:
    case SNil{}:
      pend(st)
    case SCon{+c, t}:
      List.append(&2, Piece, pout(st, c), units(t, pnext(st, c)))

# The UTF-8 reader's state: between chars, or inside one: the continuation
# bytes still needed after the next, the value so far, the next byte's range
type Utf is Data:
  UIdle{}
  UNeed{more: Nat, acc: U32, lo: U32, hi: U32}

# What one unit adds, and the state after it
type UStep is Data:
  UStep{out: String, next: Utf}

def bad() -> Char:
  Chr{65533}

def lead.four.at(f0: Bool, f1: Bool, f4: Bool, b: U32) -> UStep:
  match f0:
    case True{}:
      UStep{SNil{}, UNeed{2n, 0, 144, 191}}
    case False{}:
      match f1:
        case True{}:
          UStep{SNil{}, UNeed{2n, U32.sub(b, 240), 128, 191}}
        case False{}:
          match f4:
            case True{}:
              UStep{SNil{}, UNeed{2n, 4, 128, 143}}
            case False{}:
              UStep{SCon{bad(), SNil{}}, UIdle{}}

# a byte that leads no 1-3 byte char: a 4-byte lead, else invalid
def lead.four(+b: U32) -> UStep:
  lead.four.at(U32.is_eq(b, 240), within(b, 241, 243), U32.is_eq(b, 244), b)

def lead.three.at(e0: Bool, ed: Bool, e1: Bool, +b: U32) -> UStep:
  match e0:
    case True{}:
      UStep{SNil{}, UNeed{1n, 0, 160, 191}}
    case False{}:
      match ed:
        case True{}:
          UStep{SNil{}, UNeed{1n, 13, 128, 159}}
        case False{}:
          match e1:
            case True{}:
              UStep{SNil{}, UNeed{1n, U32.sub(b, 224), 128, 191}}
            case False{}:
              lead.four(b)

# a byte that leads no 1-2 byte char: a 3-byte lead, else lead.four
def lead.three(+b: U32) -> UStep:
  lead.three.at(U32.is_eq(b, 224), U32.is_eq(b, 237), within(b, 225, 239), b)

def lead.at(ascii: Bool, two: Bool, +b: U32) -> UStep:
  match ascii:
    case True{}:
      UStep{SCon{Chr{b}, SNil{}}, UIdle{}}
    case False{}:
      match two:
        case True{}:
          UStep{SNil{}, UNeed{0n, U32.sub(b, 192), 128, 191}}
        case False{}:
          lead.three(b)

# a byte between chars
def lead(+b: U32) -> UStep:
  lead.at(U32.is_lt(b, 128), within(b, 194, 223), b)

def cont.at(more: Nat, +v: U32) -> UStep:
  match more:
    case 0n:
      UStep{SCon{Chr{v}, SNil{}}, UIdle{}}
    case 1n+m:
      UStep{SNil{}, UNeed{m, v, 128, 191}}

def broken(s: UStep) -> UStep:
  match s:
    case UStep{o, n}:
      UStep{SCon{bad(), o}, n}

def cont(ok: Bool, more: Nat, acc: U32, +b: U32) -> UStep:
  match ok:
    case True{}:
      cont.at(more, U32.add(U32.mul(acc, 64), U32.sub(b, 128)))
    case False{}:
      broken(lead(b))

def ustep(st: Utf, u: Piece) -> UStep:
  match st:
    case UIdle{}:
      match u:
        case UChar{c}:
          UStep{SCon{c, SNil{}}, UIdle{}}
        case UByte{+b}:
          lead(b)
    case UNeed{more, acc, +lo, +hi}:
      match u:
        case UChar{c}:
          UStep{SCon{bad(), SCon{c, SNil{}}}, UIdle{}}
        case UByte{+b}:
          cont(within(b, lo, hi), more, acc, b)

def uend(st: Utf) -> String:
  match st:
    case UIdle{}:
      SNil{}
    case UNeed{more, acc, lo, hi}:
      SCon{bad(), SNil{}}

def uout(s: UStep) -> String:
  match s:
    case UStep{o, n}:
      o

def unext(s: UStep) -> Utf:
  match s:
    case UStep{o, n}:
      n

# the text of pieces, bytes read as UTF-8: each maximal invalid part U+FFFD
def utf(us: List<&2, Piece>, +st: Utf) -> String:
  match us:
    case Nil{}:
      uend(st)
    case +u <> rest:
      String.append(uout(ustep(st, u)), utf(rest, unext(ustep(st, u))))

# a decoded name or value
def decode(s: String) -> String:
  utf(units(s, PPlain{}), UIdle{})

# Parameters
# ----------

# A parameter, decoded
type Param is Data:
  Param{name: String, value: String}

def param(m: Maybe<&2, Cut>, +s: String) -> Param:
  match m:
    case None{}:
      Param{decode(s), SNil{}}
    case Some{x}:
      match x:
        case Cut{h, u}:
          Param{decode(h), decode(u)}

def params.at(empty: Bool, +p: String, r: List<&2, Param>) -> List<&2, Param>:
  match empty:
    case True{}:
      r
    case False{}:
      param(split(p, '='), p) <> r

def params.go(ps: List<&2, String>) -> List<&2, Param>:
  match ps:
    case Nil{}:
      []
    case +p <> rest:
      params.at(String.is_empty(p), p, params.go(rest))

# the parameters of a carrier, in order (empty pairs skipped)
def params(s: String) -> List<&2, Param>:
  params.go(String.split(s, '&'))

def find.at(b: Bool, v: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      r

# the first non-empty value of a name
def find(+name: String, ps: List<&2, Param>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      match p:
        case Param{n, +v}:
          find.at(Bool.and(String.eq(n, name), Bool.not(String.is_empty(v))), v, find(name, rest))

def get.at(m: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      r
    case Some{v}:
      Some{v}

# a name's value: the first carrier that has one
def get(+name: String, cs: List<&2, String>) -> Maybe<&2, String>:
  match cs:
    case Nil{}:
      None{}
    case c <> rest:
      get.at(find(name, params(c)), get(name, rest))

def from_code(m: Maybe<&2, String>, +cs: List<&2, String>) -> Answer:
  match m:
    case None{}:
      Failed{FMissing{}}
    case Some{c}:
      Pasted{c, get("state", cs)}

def from_error(m: Maybe<&2, String>, +cs: List<&2, String>) -> Answer:
  match m:
    case Some{e}:
      Failed{FProvider{e, get("error_description", cs)}}
    case None{}:
      from_code(get("code", cs), cs)

# the answer of carriers: an error wins, then the code and its state
def from_params(+cs: List<&2, String>) -> Answer:
  from_error(get("error", cs), cs)

# Parse
# -----

def key(m: Maybe<&2, Cut>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Cut{+h, u}:
          Bool.or(String.eq(h, "code"), Bool.or(String.eq(h, "state"), String.eq(h, "error")))

def carries.go(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(key(split(p, '=')), carries.go(rest))

# a text holds a `code=`, `state=` or `error=` pair
def carries(s: String) -> Bool:
  carries.go(String.split(s, '&'))

def bare.state(empty: Bool, f: String) -> Maybe<&2, String>:
  match empty:
    case True{}:
      None{}
    case False{}:
      Some{f}

def bare.at(in_head: Bool, in_frag: Bool, empty: Bool, h: String, +f: String) -> Answer:
  match in_head:
    case True{}:
      from_params([unslash(h)])
    case False{}:
      match in_frag:
        case True{}:
          from_params([f])
        case False{}:
          match empty:
            case True{}:
              Failed{FMissing{}}
            case False{}:
              Pasted{h, bare.state(String.is_empty(f), f)}

# a text without `?` or `://`: its head before the first `#`, and the
# fragment after it
def bare(+h: String, +f: String) -> Answer:
  bare.at(carries(h), carries(f), String.is_empty(h), h, f)

def parse.hash(m: Maybe<&2, Cut>, v: String) -> Answer:
  match m:
    case None{}:
      bare(v, SNil{})
    case Some{x}:
      match x:
        case Cut{h, f}:
          bare(h, f)

def parse.scheme(m: Maybe<&2, String>, +v: String) -> Answer:
  match m:
    case Some{rest}:
      from_params([fragment(split(rest, '#'))])
    case None{}:
      parse.hash(split(v, '#'), v)

def parse.query(m: Maybe<&2, Cut>, rest: String) -> Answer:
  match m:
    case None{}:
      from_params([unslash(rest), SNil{}])
    case Some{x}:
      match x:
        case Cut{q, f}:
          from_params([unslash(q), f])

def parse.at(m: Maybe<&2, Cut>, +v: String) -> Answer:
  match m:
    case Some{x}:
      match x:
        case Cut{h, +rest}:
          parse.query(split(rest, '#'), rest)
    case None{}:
      parse.scheme(scheme(v), v)

# a paste's code and state, or why it has none
def parse(s: String) -> Answer:
  +v = clean(s)
  parse.at(split(v, '?'), v)

# State check and texts
# ---------------------

def verify.at(same: Bool, code: String, s: String) -> Answer:
  match same:
    case True{}:
      Pasted{code, Some{s}}
    case False{}:
      Failed{FMismatch{}}

# a paste's state against the login's own: equal, or none (the login's)
def verify(code: String, m: Maybe<&2, String>, +expected: String) -> Answer:
  match m:
    case None{}:
      Pasted{code, Some{expected}}
    case Some{+s}:
      verify.at(String.eq(s, expected), code, s)

def described(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{d}:
      String.concat([" (", d, ")"])

# the user-facing text of a failure
def text(f: Fail) -> String:
  match f:
    case FMissing{}:
      "That address has no authorization code. Paste the full address of the page your browser ended on."
    case FMismatch{}:
      "That address is from a different login attempt (state mismatch). Paste the address from the browser tab this login opened."
    case FProvider{e, d}:
      String.concat(["The sign-in page reported an error: ", e, described(d), ". Open the login link again and sign in, then paste the new address."])

def trim_start.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_start.at(Ga.space(c), c, t, trim_start(t))

def dots.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def dots(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      dots.at(Char.is_eq(c, '.'), c, t, dots(t))

# the reason of a failed exchange: trimmed, then its trailing `.`s dropped
def reason(s: String) -> String:
  String.reverse(dots(trim_start(String.reverse(trim_start(s)))))

# the notice of a failed token exchange
def notice(s: String) -> String:
  String.concat(["Login did not complete: ", reason(s), ". Paste the address again, or open the login link again and sign in."])
