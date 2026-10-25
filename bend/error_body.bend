# error_body: what a provider's HTTP error shows its user (Rust: eukhe-ai
# utils/error_body.rs `normalize_provider_error`, `format_provider_error`,
# `truncate_error_text`; laws/error_body.bend). An SDK keeps the body of a
# failed request in one of three places, each probed in turn: Mistral's
# `body` (a JSON string), `openai`'s parsed `error` (a plain object with a
# key), Bedrock's `$response.body` (either). The body is trimmed as JS
# `String.prototype.trim` does, dropped when empty, and cut to 4000 UTF-16
# code units with a marker. Rust reads the SDK's fields, serializes an
# object body, renders the status (a JSON number) as JS does and finds
# whether the message already holds the body (a substring search, linear
# in Rust). Pure: no IO, no @unsafe.

import Base

# What one place of the error holds
type Probe is Data:
  # nothing there, or a value that is neither a text nor an object with a key
  PNone{}
  # a JSON string
  PText{s: String}
  # a plain JSON object with at least one key, serialized
  PObj{s: String}

# Text
# ----

# JS white space and line terminators (what `trim` drops): U+0009..U+000D,
# U+0020, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F, U+205F,
# U+3000, U+FEFF (not U+0085)
def is_ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))))))))

# yes, run, when b; else no
def when(b: Bool, yes: Unit -> String, no: String) -> String:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no

# s without its leading white space
def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      when(is_ws(c), u => trim_start(t), SCon{c, t})

def trim_end.last(c: Char, ws: Bool) -> String:
  match ws:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, SNil{}}

def trim_end.at(+c: Char, r: String) -> String:
  match r:
    case SNil{}:
      trim_end.last(c, is_ws(c))
    case SCon{d, u}:
      SCon{c, SCon{d, u}}

# s without its trailing white space
def trim_end(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      trim_end.at(c, trim_end(t))

# JS `trim`
def trim(s: String) -> String:
  trim_end(trim_start(s))

def units1.at(astral: Bool) -> Nat:
  match astral:
    case True{}:
      2n
    case False{}:
      1n

# the UTF-16 code units of a char: 2 past U+FFFF
def units1(c: Char) -> Nat:
  units1.at(U32.is_le(65536, Char.to_u32(c)))

# JS `length`: the UTF-16 code units of s
def units(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      Nat.add(units1(c), units(t))

# the longest prefix of s within `room` UTF-16 code units that splits no
# char
def prefix(s: String, +room: Nat) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      +need = units1(c)
      when(Nat.is_le(need, room), u => SCon{c, prefix(t, Nat.sub(room, need))}, SNil{})

def truncate.at(+text: String, +max: Nat, +n: Nat, fits: Bool) -> String:
  match fits:
    case True{}:
      text
    case False{}:
      String.concat([prefix(text, max), "... [truncated ", Nat.show(Nat.sub(n, max)), " chars]"])

# text cut to `max` UTF-16 code units, with a marker that counts the units
# cut
def truncate(+text: String, +max: Nat) -> String:
  +n = units(text)
  truncate.at(text, max, n, Nat.is_le(n, max))

# The body
# --------

# the cap on the body a provider error shows
def body_cap() -> Nat:
  4000n

def pick.response(r: Probe) -> Maybe<&2, String>:
  match r:
    case PNone{}:
      None{}
    case PText{s}:
      Some{s}
    case PObj{s}:
      Some{s}

def pick.error(e: Probe, r: Probe) -> Maybe<&2, String>:
  match e:
    case PObj{s}:
      Some{s}
    case PNone{}:
      pick.response(r)
    case PText{s}:
      pick.response(r)

# the first usable body: Mistral's text, `openai`'s object, Bedrock's text
# or object
def pick(b: Probe, e: Probe, r: Probe) -> Maybe<&2, String>:
  match b:
    case PText{s}:
      Some{s}
    case PNone{}:
      pick.error(e, r)
    case PObj{s}:
      pick.error(e, r)

def body.of(t: String) -> Maybe<&2, String>:
  match t:
    case SNil{}:
      None{}
    case SCon{c, u}:
      Some{truncate(SCon{c, u}, body_cap())}

def body.trim(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      body.of(trim(s))

# the body the error shows: the first usable one, trimmed, none when
# empty, cut to the cap
def body(b: Probe, e: Probe, r: Probe) -> Maybe<&2, String>:
  body.trim(pick(b, e, r))

# The display string
# ------------------

def show.plain(prefix: Maybe<&2, String>, status: Maybe<&2, String>, +message: String) -> String:
  match prefix status:
    case Some{p} Some{st}:
      String.concat([p, " (", st, "): ", message])
    case Some{p} None{}:
      message
    case None{} _:
      message

def show.body(prefix: Maybe<&2, String>, st: String, b: String) -> String:
  match prefix:
    case Some{p}:
      String.concat([p, " (", st, "): ", b])
    case None{}:
      String.concat([st, ": ", b])

# the error's display string: the status and the body when the message
# lacks the body, else the message (after the prefix and the status, when
# both are given)
def show(carried: Bool, status: Maybe<&2, String>, b: Maybe<&2, String>, prefix: Maybe<&2, String>, +message: String) -> String:
  match carried status b:
    case False{} Some{st} Some{x}:
      show.body(prefix, st, x)
    case False{} Some{st} None{}:
      show.plain(prefix, Some{st}, message)
    case False{} None{} _:
      show.plain(prefix, None{}, message)
    case True{} _ _:
      show.plain(prefix, status, message)
