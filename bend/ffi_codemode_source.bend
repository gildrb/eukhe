# ffi_codemode_source: the entry of the compiled Bend core for what a code
# mode tool input is (bend/codemode_source.bend; Rust:
# crates/eukhe-durable/src/codemode/source.rs through
# `eukhe_bend::rules::codemode_source`, once per code mode call). The
# request is the input's facts (crates/eukhe-bend/WIRE.md is the grammar):
#
#   Num    0 (no safe integer) | 1 Nat (the integer, saturated)
#   Field  String (its key), Num (its value)
#   Json   0 String (serde_json's error) | 1 (no object) | 2 List<Field>
#   Dir    Bool (empty), Json
#   Facts  Bool (blank), List<Nat> (the options lines after the first,
#          0-based), Bool (the text from the first newline on is blank),
#          Maybe<Dir> (the first line's directive)
#
#   reply  0 String (refused, the text) | 1 (plain) | 2 Bool Bool (split:
#          max_output_tokens set, timeout_ms set)
#
# Malformed input, or input left after the request, answers
# `E codemode_source: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./codemode_source.bend as Src

# Facts
# -----

def get_num.n(r: W.Dec<Nat>) -> W.Dec<Src.Num>:
  match r:
    case W.Got{n, s}:
      W.Got{Src.Int{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_num.tag(r: W.Dec<Nat>) -> W.Dec<Src.Num>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Src.NoInt{}, s}
        case 1n:
          get_num.n(W.get_nat(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a value: its tag, then its integer
def get_num(s: String) -> W.Dec<Src.Num>:
  get_num.tag(W.get_nat(s))

def get_field.num(k: String, r: W.Dec<Src.Num>) -> W.Dec<Src.Field>:
  match r:
    case W.Got{v, s}:
      W.Got{Src.Field{k, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_field.key(r: W.Dec<String>) -> W.Dec<Src.Field>:
  match r:
    case W.Got{k, s}:
      get_field.num(k, get_num(s))
    case W.Bad{}:
      W.Bad{}

# a field: its key, then its value
def get_field(s: String) -> W.Dec<Src.Field>:
  get_field.key(W.get_str(s))

def get_json.fields(r: W.Dec<List<&2, Src.Field>>) -> W.Dec<Src.Json>:
  match r:
    case W.Got{fs, s}:
      W.Got{Src.Obj{fs}, s}
    case W.Bad{}:
      W.Bad{}

def get_json.text(r: W.Dec<String>) -> W.Dec<Src.Json>:
  match r:
    case W.Got{t, s}:
      W.Got{Src.JsonErr{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_json.tag(r: W.Dec<Nat>) -> W.Dec<Src.Json>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_json.text(W.get_str(s))
        case 1n:
          W.Got{Src.NotObj{}, s}
        case 2n:
          get_json.fields(W.get_list(~Src.Field, ~get_field, s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# what serde_json read: its tag, then its error text or fields
def get_json(s: String) -> W.Dec<Src.Json>:
  get_json.tag(W.get_nat(s))

def get_dir.json(e: Bool, r: W.Dec<Src.Json>) -> W.Dec<Src.Dir>:
  match r:
    case W.Got{j, s}:
      W.Got{Src.Dir{e, j}, s}
    case W.Bad{}:
      W.Bad{}

def get_dir.empty(r: W.Dec<Bool>) -> W.Dec<Src.Dir>:
  match r:
    case W.Got{e, s}:
      get_dir.json(e, get_json(s))
    case W.Bad{}:
      W.Bad{}

# a directive: empty, then what serde_json read
def get_dir(s: String) -> W.Dec<Src.Dir>:
  get_dir.empty(W.get_bool(s))

def get_mdir.dir(r: W.Dec<Src.Dir>) -> W.Dec<Maybe<&2, Src.Dir>>:
  match r:
    case W.Got{d, s}:
      W.Got{Some{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_mdir.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Src.Dir>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mdir.dir(get_dir(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the first line's directive, if it is an options line
def get_mdir(s: String) -> W.Dec<Maybe<&2, Src.Dir>>:
  get_mdir.tag(W.get_nat(s))

# Requests
# --------

def get_req.dir(b: Bool, ms: List<&2, Nat>, rb: Bool, r: W.Dec<Maybe<&2, Src.Dir>>) -> W.Dec<Src.Facts>:
  match r:
    case W.Got{m, s}:
      W.Got{Src.Facts{b, ms, rb, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.rest(b: Bool, ms: List<&2, Nat>, r: W.Dec<Bool>) -> W.Dec<Src.Facts>:
  match r:
    case W.Got{rb, s}:
      get_req.dir(b, ms, rb, get_mdir(s))
    case W.Bad{}:
      W.Bad{}

def get_req.marks(b: Bool, r: W.Dec<List<&2, Nat>>) -> W.Dec<Src.Facts>:
  match r:
    case W.Got{ms, s}:
      get_req.rest(b, ms, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.blank(r: W.Dec<Bool>) -> W.Dec<Src.Facts>:
  match r:
    case W.Got{b, s}:
      get_req.marks(b, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

# a request: the facts of an input
def get_req(s: String) -> W.Dec<Src.Facts>:
  get_req.blank(W.get_bool(s))

# Replies
# -------

# the answer: refused with its text, plain, or split with the options set
def put_answer(a: Src.Answer) -> String:
  match a:
    case Src.Refuse{t}:
      W.put_nat(0n, W.put_str(t, ""))
    case Src.Plain{}:
      W.put_nat(1n, "")
    case Src.Split{k, o}:
      W.put_nat(2n, W.put_bool(k, W.put_bool(o, "")))

# The entry
# ---------

def ffi.done(f: Src.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_answer(Src.parse(f))
    case False{}:
      W.err("codemode_source: malformed request")

def ffi.got(r: W.Dec<Src.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("codemode_source: malformed request")

# the entry: decode the facts, answer what the input is
def ffi(input: String) -> String:
  ffi.got(get_req(input))
