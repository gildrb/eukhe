# codemode_source: what a code mode tool input is (port of pi-codemode
# `source.ts`; the Rust host is crates/eukhe-durable/src/codemode/source.rs):
# a script, a script after a first-line options directive with the
# options it sets, or a refusal with its text. The host reads the text
# facts of the input: whether it is blank (Rust `trim`), which lines after
# the first are options lines (a line whose text after leading White_Space
# starts with `// @options:`), whether the text from the first newline on
# is blank, and, when the first line is an options line, its directive:
# whether it is empty and what serde_json reads from it (an error text, a
# value that is no object, or an object's fields in order, each with its
# value as a JS safe non-negative integer when it is one, saturated at the
# wire's largest Nat). This model decides every refusal and its text, which
# line is misplaced and its number, the JS `Object.keys` order of the keys
# (array indexes first, by index), and which options the directive sets.
# Pure: no IO, no @unsafe. laws/codemode_source.bend states its laws.

import Base
import ./wire.bend as W

# Facts
# -----

# a directive field's value: a JS safe non-negative integer (saturated at
# the wire's largest Nat), or anything else
type Num is Data:
  NoInt{}
  Int{n: Nat}

# a field of the directive's object: its key and its value
type Field is Data:
  Field{key: String, num: Num}

# what serde_json reads from the directive
type Json is Data:
  # invalid JSON: serde_json's error text
  JsonErr{text: String}
  # a value that is no object
  NotObj{}
  # an object: its fields in order
  Obj{fields: List<&2, Field>}

# the first line's directive: the text after `// @options:`, trimmed
type Dir is Data:
  Dir{empty: Bool, json: Json}

# the facts of an input: blank, the 0-based numbers of the options lines
# after the first (in order), the text from the first newline on blank (no
# newline: blank), and the directive when the first line is an options line
type Facts is Data:
  Facts{blank: Bool, marks: List<&2, Nat>, rest_blank: Bool, dir: Maybe<&2, Dir>}

# what the input is
type Answer is Data:
  # refused, with the text the script's caller gets
  Refuse{text: String}
  # the whole input is the script; no options
  Plain{}
  # the script is the text from the first newline on; the options take the
  # given `max_output_tokens` (tokens) and `timeout_ms` (timeout) when set
  Split{tokens: Bool, timeout: Bool}

# An array index (`Object.keys` lists them first, by index)
# --------------------------------------------------------

# the largest array index is one less (2^32 - 2): JS reserves 2^32 - 1
def index_cap() -> Nat:
  4294967295n

def index.at(below: Bool, n: Nat) -> Maybe<&2, Nat>:
  match below:
    case True{}:
      Some{n}
    case False{}:
      None{}

def index.got(d: W.Dec<Nat>) -> Maybe<&2, Nat>:
  match d:
    case W.Got{+n, r}:
      match r:
        case SNil{}:
          index.at(Nat.is_lt(n, index_cap()), n)
        case SCon{c, t}:
          None{}
    case W.Bad{}:
      None{}

# the index of an array-index key: its canonical decimal (no sign, no
# leading zero, "0" alone) below 2^32 - 1, read with the wire's Nat reader
# (which refuses a 15th digit, so no long key folds past the runtime's Nat)
def index(key: String) -> Maybe<&2, Nat>:
  index.got(W.get_nat(String.append(key, ",")))

# The first unsupported key
# -------------------------

# an array-index key and its index
type Ix is Data:
  Ix{n: Nat, key: String}

def least.cmp(earlier: Bool, n: Nat, key: String, best: Ix) -> Maybe<&2, Ix>:
  match earlier:
    case True{}:
      Some{best}
    case False{}:
      Some{Ix{n, key}}

def least.with(+n: Nat, key: String, rest: Maybe<&2, Ix>) -> Maybe<&2, Ix>:
  match rest:
    case None{}:
      Some{Ix{n, key}}
    case Some{b}:
      match b:
        case Ix{+m, k}:
          least.cmp(Nat.is_lt(m, n), n, key, Ix{m, k})

def least.pick(m: Maybe<&2, Nat>, key: String, rest: Maybe<&2, Ix>) -> Maybe<&2, Ix>:
  match m:
    case None{}:
      rest
    case Some{n}:
      least.with(n, key, rest)

# the array-index key of fs with the least index (of equal ones, the first)
def least(fs: List<&2, Field>) -> Maybe<&2, Ix>:
  match fs:
    case Nil{}:
      None{}
    case f <> r:
      match f:
        case Field{+k, v}:
          least.pick(index(k), k, least(r))

# the key is `max_output_tokens` or `timeout_ms`
def supported(+key: String) -> Bool:
  Bool.or(String.eq(key, "max_output_tokens"), String.eq(key, "timeout_ms"))

def other.pick(ok: Bool, key: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{key}

# the first key of fs that is not supported
def other(fs: List<&2, Field>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case f <> r:
      match f:
        case Field{+k, v}:
          other.pick(supported(k), k, other(r))

def unsupported.or(l: Maybe<&2, Ix>, fs: List<&2, Field>) -> Maybe<&2, String>:
  match l:
    case Some{b}:
      match b:
        case Ix{n, k}:
          Some{k}
    case None{}:
      other(fs)

# the first key of `Object.keys(fields)` that is not supported: the array
# index keys come first, by index, and are never supported
def unsupported(+fs: List<&2, Field>) -> Maybe<&2, String>:
  unsupported.or(least(fs), fs)

def lookup.pick(hit: Bool, v: Num, rest: Maybe<&2, Num>) -> Maybe<&2, Num>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

# the value of the first field of fs named `name`
def lookup(fs: List<&2, Field>, +name: String) -> Maybe<&2, Num>:
  match fs:
    case Nil{}:
      None{}
    case f <> r:
      match f:
        case Field{k, v}:
          lookup.pick(String.eq(k, name), v, lookup(r, name))

# Texts
# -----

def fields_text() -> String:
  "`max_output_tokens` and `timeout_ms`"

def blank_text() -> String:
  "Expected JavaScript source text (non-empty). Provide JS only, optionally with a first line `// @options: {\"max_output_tokens\": 1000}`."

def misplaced_text(line: Nat) -> String:
  String.append("The // @options: line must be the first line of the input; found one on line ", Nat.show(line))

def no_code_text() -> String:
  "The @options line must be followed by JavaScript source on subsequent lines"

def object_text() -> String:
  String.append("@options must be a JSON object with supported fields ", fields_text())

def json_text(err: String) -> String:
  String.append(String.append("@options must be valid JSON with supported fields ", String.append(fields_text(), ": ")), err)

def key_text(key: String) -> String:
  String.concat(["@options only supports ", fields_text(), "; got `", key, "`"])

def tokens_text() -> String:
  "@options field `max_output_tokens` must be a non-negative safe integer"

def timeout_text() -> String:
  "@options field `timeout_ms` must be a positive integer up to 2147483647"

# The options
# -----------

# a `timeout_ms` in 1..=2147483647 (the largest `setTimeout` delay)
def timeout_ok(+n: Nat) -> Bool:
  Bool.and(Nat.is_le(1n, n), Nat.is_le(n, 2147483647n))

def options.range(tok: Bool, ok: Bool) -> Answer:
  match ok:
    case True{}:
      Split{tok, True{}}
    case False{}:
      Refuse{timeout_text()}

def options.timeout(tok: Bool, m: Maybe<&2, Num>) -> Answer:
  match m:
    case None{}:
      Split{tok, False{}}
    case Some{v}:
      match v:
        case NoInt{}:
          Refuse{timeout_text()}
        case Int{n}:
          options.range(tok, timeout_ok(n))

def options.tokens(m: Maybe<&2, Num>, +fs: List<&2, Field>) -> Answer:
  match m:
    case None{}:
      options.timeout(False{}, lookup(fs, "timeout_ms"))
    case Some{v}:
      match v:
        case NoInt{}:
          Refuse{tokens_text()}
        case Int{n}:
          options.timeout(True{}, lookup(fs, "timeout_ms"))

def options.keys(bad: Maybe<&2, String>, +fs: List<&2, Field>) -> Answer:
  match bad:
    case Some{k}:
      Refuse{key_text(k)}
    case None{}:
      options.tokens(lookup(fs, "max_output_tokens"), fs)

def options.json(j: Json) -> Answer:
  match j:
    case JsonErr{t}:
      Refuse{json_text(t)}
    case NotObj{}:
      Refuse{object_text()}
    case Obj{+fs}:
      options.keys(unsupported(fs), fs)

# the options of a directive
def options(d: Dir) -> Answer:
  match d:
    case Dir{empty, j}:
      match empty:
        case True{}:
          Refuse{object_text()}
        case False{}:
          options.json(j)

# The input
# ---------

def parse.dir(m: Maybe<&2, Dir>, rb: Bool) -> Answer:
  match m:
    case None{}:
      Plain{}
    case Some{d}:
      match rb:
        case True{}:
          Refuse{no_code_text()}
        case False{}:
          options(d)

def parse.marks(ms: List<&2, Nat>, rb: Bool, m: Maybe<&2, Dir>) -> Answer:
  match ms:
    case Nil{}:
      parse.dir(m, rb)
    case k <> t:
      Refuse{misplaced_text(1n+k)}

# what an input with facts f is: blank, an options line after the first
# line (the first one, numbered from 1), a plain script, or a script after
# the options line (refused when nothing but blank text follows it)
def parse(f: Facts) -> Answer:
  match f:
    case Facts{blank, ms, rb, m}:
      match blank:
        case True{}:
          Refuse{blank_text()}
        case False{}:
          parse.marks(ms, rb, m)
