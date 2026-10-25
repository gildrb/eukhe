# eukhe: the laws of area codemode_source

import Base
import ../bend/codemode_source.bend as Src
import ../bend/ffi_codemode_source.bend as FSrc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1-R8): what a code mode tool input is (bend/codemode_source.bend,
# the port of eukhe-durable codemode/source.rs `parse_codemode_source`,
# pi-codemode `source.ts`). Each law is an open claim about Src.parse or
# Src.index; PROOF.bend proves them (as CodemodeSource.<law>) with the
# lemmas of proof/codemode_source/.
#
# The host gives the input's text facts: whether it is blank (Rust
# `trim`), the 0-based numbers of the lines after the first that are
# options lines (the text after leading White_Space starts with
# `// @options:`), whether the text from the first newline on is blank
# (blank when there is no newline), and, when the first line is an options
# line, its directive (the text after `// @options:`, trimmed): whether it
# is empty and what serde_json reads from it: an error text, a value that
# is no object, or an object's fields in order (keys distinct), each with
# its value as a JS safe non-negative integer (saturated) or not one.
#
# R1: a blank input is refused with "Expected JavaScript source text
#     (non-empty). Provide JS only, optionally with a first line `//
#     @options: {"max_output_tokens": 1000}`."
# R2: else an options line after the first line is refused with "The //
#     @options: line must be the first line of the input; found one on line
#     <n>", n the number (from 1) of the first one listed.
# R3: else an input whose first line is no options line is the script as
#     a whole, with no options (Plain).
# R4: else the script is the text from the first newline on, and the
#     input is refused when that text is blank: "The @options line must be
#     followed by JavaScript source on subsequent lines".
# R5: an empty directive, or one whose JSON is no object, is refused with
#     "@options must be a JSON object with supported fields
#     `max_output_tokens` and `timeout_ms`"; invalid JSON with "@options
#     must be valid JSON with supported fields `max_output_tokens` and
#     `timeout_ms`: " and serde_json's text.
# R6: the first key of JS `Object.keys` order that is not
#     `max_output_tokens` or `timeout_ms` is refused with "@options only
#     supports `max_output_tokens` and `timeout_ms`; got `<key>`". The
#     order lists the array-index keys first (a key that is the canonical
#     decimal spelling of an n below 2^32 - 1: no sign, no leading zero,
#     "0" alone), by index (of equal ones the first), then the other keys
#     in their order.
# R7: a `max_output_tokens` that is no safe non-negative integer is
#     refused with "@options field `max_output_tokens` must be a
#     non-negative safe integer"; then a `timeout_ms` that is no integer in
#     1..=2147483647 with "@options field `timeout_ms` must be a positive
#     integer up to 2147483647".
# R8: else the script follows the options line (Split), and the options
#     set exactly the fields present.

# Terms
# -----

# R1-R7: the refusal texts, restated from source.rs
def blank_spec() -> String:
  "Expected JavaScript source text (non-empty). Provide JS only, optionally with a first line `// @options: {\"max_output_tokens\": 1000}`."

def misplaced_spec(n: Nat) -> String:
  String.append("The // @options: line must be the first line of the input; found one on line ", Nat.show(n))

def no_code_spec() -> String:
  "The @options line must be followed by JavaScript source on subsequent lines"

def object_spec() -> String:
  "@options must be a JSON object with supported fields `max_output_tokens` and `timeout_ms`"

def json_spec(err: String) -> String:
  String.append("@options must be valid JSON with supported fields `max_output_tokens` and `timeout_ms`: ", err)

def key_spec(key: String) -> String:
  String.concat(["@options only supports `max_output_tokens` and `timeout_ms`; got `", key, "`"])

def tokens_spec() -> String:
  "@options field `max_output_tokens` must be a non-negative safe integer"

def timeout_spec() -> String:
  "@options field `timeout_ms` must be a positive integer up to 2147483647"

def ix_one(m: Maybe<&2, Nat>, k: String, rest: List<&2, Src.Ix>) -> List<&2, Src.Ix>:
  match m:
    case None{}:
      rest
    case Some{n}:
      Src.Ix{n, k} <> rest

# R6: the array-index keys of fs with their indexes, in order (an index is
# pinned by codemode_source_index_spelled and _reads)
def ixs_spec(fs: List<&2, Src.Field>) -> List<&2, Src.Ix>:
  match fs:
    case Nil{}:
      []
    case f <> r:
      match f:
        case Src.Field{+k, v}:
          ix_one(Src.index(k), k, ixs_spec(r))

# x, unless the later y has a smaller index
def least_of(later_less: Bool, x: Src.Ix, y: Src.Ix) -> Src.Ix:
  match later_less:
    case True{}:
      y
    case False{}:
      x

def least_first(x: Src.Ix, best: Maybe<&2, Src.Ix>) -> Src.Ix:
  match x:
    case Src.Ix{+n, k}:
      match best:
        case None{}:
          Src.Ix{n, k}
        case Some{y}:
          match y:
            case Src.Ix{+m, k2}:
              least_of(Nat.is_lt(m, n), Src.Ix{n, k}, Src.Ix{m, k2})

# R6: the least of xs by index, the first of equal ones
def least_spec(xs: List<&2, Src.Ix>) -> Maybe<&2, Src.Ix>:
  match xs:
    case Nil{}:
      None{}
    case x <> r:
      Some{least_first(x, least_spec(r))}

# R6: the supported keys
def supported_spec(+k: String) -> Bool:
  Bool.or(String.eq(k, "max_output_tokens"), String.eq(k, "timeout_ms"))

def other_at(ok: Bool, k: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{k}

# R6: the first key of fs that is not supported
def other_spec(fs: List<&2, Src.Field>) -> Maybe<&2, String>:
  match fs:
    case Nil{}:
      None{}
    case f <> r:
      match f:
        case Src.Field{+k, v}:
          other_at(supported_spec(k), k, other_spec(r))

def unsupported_pick(l: Maybe<&2, Src.Ix>, fs: List<&2, Src.Field>) -> Maybe<&2, String>:
  match l:
    case Some{b}:
      match b:
        case Src.Ix{n, k}:
          Some{k}
    case None{}:
      other_spec(fs)

# R6: the first unsupported key of `Object.keys` order
def unsupported_spec(+fs: List<&2, Src.Field>) -> Maybe<&2, String>:
  unsupported_pick(least_spec(ixs_spec(fs)), fs)

def find_at(hit: Bool, v: Src.Num, rest: Maybe<&2, Src.Num>) -> Maybe<&2, Src.Num>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

# the value of the first field of fs named k
def find_spec(fs: List<&2, Src.Field>, +k: String) -> Maybe<&2, Src.Num>:
  match fs:
    case Nil{}:
      None{}
    case f <> r:
      match f:
        case Src.Field{k2, v}:
          find_at(String.eq(k2, k), v, find_spec(r, k))

# R7: a `timeout_ms` in 1..=2147483647
def timeout_in(+n: Nat) -> Bool:
  Bool.and(Nat.is_le(1n, n), Nat.is_le(n, 2147483647n))

def timeout_at(ok: Bool, tok: Bool) -> Src.Answer:
  match ok:
    case True{}:
      Src.Split{tok, True{}}
    case False{}:
      Src.Refuse{timeout_spec()}

def timeout_num(v: Src.Num, tok: Bool) -> Src.Answer:
  match v:
    case Src.NoInt{}:
      Src.Refuse{timeout_spec()}
    case Src.Int{n}:
      timeout_at(timeout_in(n), tok)

# R7-R8: the timeout's check after the tokens' (tok: tokens present)
def timeout_step(m: Maybe<&2, Src.Num>, tok: Bool) -> Src.Answer:
  match m:
    case None{}:
      Src.Split{tok, False{}}
    case Some{v}:
      timeout_num(v, tok)

def tokens_step(m: Maybe<&2, Src.Num>, +fs: List<&2, Src.Field>) -> Src.Answer:
  match m:
    case None{}:
      timeout_step(find_spec(fs, "timeout_ms"), False{})
    case Some{v}:
      match v:
        case Src.NoInt{}:
          Src.Refuse{tokens_spec()}
        case Src.Int{n}:
          timeout_step(find_spec(fs, "timeout_ms"), True{})

def keys_step(bad: Maybe<&2, String>, +fs: List<&2, Src.Field>) -> Src.Answer:
  match bad:
    case Some{k}:
      Src.Refuse{key_spec(k)}
    case None{}:
      tokens_step(find_spec(fs, "max_output_tokens"), fs)

def json_step(j: Src.Json) -> Src.Answer:
  match j:
    case Src.JsonErr{t}:
      Src.Refuse{json_spec(t)}
    case Src.NotObj{}:
      Src.Refuse{object_spec()}
    case Src.Obj{+fs}:
      keys_step(unsupported_spec(fs), fs)

# R5-R8: what a directive gives
def dir_spec(d: Src.Dir) -> Src.Answer:
  match d:
    case Src.Dir{empty, j}:
      match empty:
        case True{}:
          Src.Refuse{object_spec()}
        case False{}:
          json_step(j)

def first_line_spec(m: Maybe<&2, Src.Dir>, rb: Bool) -> Src.Answer:
  match m:
    case None{}:
      Src.Plain{}
    case Some{d}:
      match rb:
        case True{}:
          Src.Refuse{no_code_spec()}
        case False{}:
          dir_spec(d)

# R1-R8: what an input with facts f is
def answer_spec(f: Src.Facts) -> Src.Answer:
  match f:
    case Src.Facts{blank, ms, rb, m}:
      match blank:
        case True{}:
          Src.Refuse{blank_spec()}
        case False{}:
          match ms:
            case k <> t:
              Src.Refuse{misplaced_spec(Nat.add(1n, k))}
            case Nil{}:
              first_line_spec(m, rb)

# Laws
# ----

# LAW codemode_source_exact: what every input is follows R1-R8: blank, then the first misplaced options line by its number from 1, then a plain script, then no code after the options line, then an empty or invalid directive or no object, then the first unsupported key in Object.keys order, then a bad max_output_tokens, then a bad timeout_ms, else a split setting exactly the fields present
# EXCLUDES: a check in another order, a line numbered from 0, the last
#   misplaced line named, an options line after a blank first line
#   ignored, a misplaced line ignored when the first line is no options
#   line, an empty directive read as an empty object, a key named out of
#   JS order (the first key, the last index, an index read as a string
#   key), a supported key refused, a timeout of 0 or 2147483648 accepted,
#   1 or 2147483647 refused, an option set that is absent, any changed word
law codemode_source_exact:
  for +f: Src.Facts
  {Src.parse(f) == answer_spec(f) : Src.Answer}

# LAW codemode_source_index_spelled: a key read as an array index n is the decimal spelling of n (no sign, no leading zero) and n is below 2^32 - 1
# EXCLUDES: "07", "+7", " 7", "7.0", "1e3" or "4294967295" read as an
#   index; a key read as another number
law codemode_source_index_spelled:
  for +k: String
  for +n: Nat
  for e: {Src.index(k) == Some{n} : Maybe<&2, Nat>}
  {String.append(k, ",") == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}

# LAW codemode_source_index_reads: the decimal spelling of every n below 2^32 - 1 is the array index n (it has at most 10 digits)
# EXCLUDES: an index key read as a string key (sorted in its place), the
#   bound lowered
law codemode_source_index_reads:
  for +k: String
  for +n: Nat
  for below: {Nat.is_lt(n, 4294967295n) == True{} : Bool}
  for short: {Nat.is_le(String.length(k), 10n) == True{} : Bool}
  for e: {String.append(k, ",") == LawsBase.wire_dec(n, "") : String}
  {Src.index(k) == Some{n} : Maybe<&2, Nat>}

# LAW codemode_source_example: anchor: the inputs of source.rs's tests: a misplaced line, the split options, a timeout of 0, a key order, options with no code, an empty directive, a fractional max_output_tokens, and short index keys
# EXCLUDES: a spec that is wrong on the shipped cases
law codemode_source_example:
  {Src.parse(Src.Facts{False{}, [2n], False{}, None{}}) == Src.Refuse{"The // @options: line must be the first line of the input; found one on line 3"} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], False{}, Some{Src.Dir{False{}, Src.Obj{[Src.Field{"max_output_tokens", Src.Int{2000n}}, Src.Field{"timeout_ms", Src.Int{30000n}}]}}}}) == Src.Split{True{}, True{}} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], False{}, Some{Src.Dir{False{}, Src.Obj{[Src.Field{"timeout_ms", Src.Int{0n}}]}}}}) == Src.Refuse{"@options field `timeout_ms` must be a positive integer up to 2147483647"} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], False{}, Some{Src.Dir{False{}, Src.Obj{[Src.Field{"timeout_ms", Src.Int{1n}}, Src.Field{"b", Src.Int{2n}}, Src.Field{"7", Src.Int{3n}}]}}}}) == Src.Refuse{"@options only supports `max_output_tokens` and `timeout_ms`; got `7`"} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], True{}, Some{Src.Dir{False{}, Src.Obj{[]}}}}) == Src.Refuse{"The @options line must be followed by JavaScript source on subsequent lines"} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], False{}, Some{Src.Dir{True{}, Src.JsonErr{"EOF"}}}}) == Src.Refuse{"@options must be a JSON object with supported fields `max_output_tokens` and `timeout_ms`"} : Src.Answer} &
  {Src.parse(Src.Facts{False{}, [], False{}, Some{Src.Dir{False{}, Src.Obj{[Src.Field{"max_output_tokens", Src.NoInt{}}]}}}}) == Src.Refuse{"@options field `max_output_tokens` must be a non-negative safe integer"} : Src.Answer} &
  {[Src.index("7"), Src.index("0"), Src.index("07"), Src.index(""), Src.index("1,"), Src.index("x")] == [Some{7n}, Some{0n}, None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, Nat>>}

# LAWS (R9): the entry of the compiled Bend core
# (bend/ffi_codemode_source.bend, called by crates/eukhe-durable
# codemode/source.rs through `eukhe_bend::rules::codemode_source`). Each
# law is an open claim about FSrc.ffi, stated with spec spellers built
# only from the wire primitives of bend/wire.bend (their round trips:
# laws/wire.bend).
#
# R9: a request is the facts: a Bool (blank), a List<Nat> (the options
#     lines after the first), a Bool (the text from the first newline on is
#     blank), a Maybe of the directive (0 none, 1 then a Bool (empty) and
#     what serde_json read: 0 then its error text (a String), 1 (no
#     object), 2 then a List of fields (its key, a String, then its value:
#     0 no safe integer, 1 then the integer, a Nat)). The reply is the
#     answer: 0 then the refusal text (a String), 1 (plain), or 2 then two
#     Bools (max_output_tokens set, timeout_ms set). Every input that is not
#     exactly one request whose counts, numbers and lengths fit the wire
#     answers the error form "codemode_source: malformed request"; never a
#     default.

# Spec spellers
# -------------

def spell_num(v: Src.Num, rest: String) -> String:
  match v:
    case Src.NoInt{}:
      Wr.put_nat(0n, rest)
    case Src.Int{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def spell_field(f: Src.Field, rest: String) -> String:
  match f:
    case Src.Field{k, v}:
      Wr.put_str(k, spell_num(v, rest))

def spell_fields.items(fs: List<&2, Src.Field>, rest: String) -> String:
  match fs:
    case Nil{}:
      rest
    case f <> r:
      spell_field(f, spell_fields.items(r, rest))

def spell_json(j: Src.Json, rest: String) -> String:
  match j:
    case Src.JsonErr{t}:
      Wr.put_nat(0n, Wr.put_str(t, rest))
    case Src.NotObj{}:
      Wr.put_nat(1n, rest)
    case Src.Obj{+fs}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, Src.Field, fs), spell_fields.items(fs, rest)))

def spell_dir(d: Src.Dir, rest: String) -> String:
  match d:
    case Src.Dir{e, j}:
      Wr.put_bool(e, spell_json(j, rest))

def spell_mdir(m: Maybe<&2, Src.Dir>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{d}:
      Wr.put_nat(1n, spell_dir(d, rest))

# a request, then rest
def spell_req(f: Src.Facts, rest: String) -> String:
  match f:
    case Src.Facts{b, ms, rb, m}:
      Wr.put_bool(b, LawsBase.wire_spell_nats(ms, Wr.put_bool(rb, spell_mdir(m, rest))))

def spell_answer(a: Src.Answer) -> String:
  match a:
    case Src.Refuse{t}:
      Wr.put_nat(0n, Wr.put_str(t, ""))
    case Src.Plain{}:
      Wr.put_nat(1n, "")
    case Src.Split{k, o}:
      Wr.put_nat(2n, Wr.put_bool(k, Wr.put_bool(o, "")))

# the reply Rust reads: the spelled answer of the model
def spell_reply(f: Src.Facts) -> String:
  spell_answer(Src.parse(f))

def num_fits(v: Src.Num) -> Bool:
  match v:
    case Src.NoInt{}:
      True{}
    case Src.Int{n}:
      LawsBase.wire_fits(n)

def field_fits(f: Src.Field) -> Bool:
  match f:
    case Src.Field{k, v}:
      Bool.and(LawsBase.wire_fits(String.length(k)), num_fits(v))

def fields_all(fs: List<&2, Src.Field>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> r:
      Bool.and(field_fits(f), fields_all(r))

def json_fits(j: Src.Json) -> Bool:
  match j:
    case Src.JsonErr{t}:
      LawsBase.wire_fits(String.length(t))
    case Src.NotObj{}:
      True{}
    case Src.Obj{+fs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Src.Field, fs)), fields_all(fs))

def dir_fits(d: Src.Dir) -> Bool:
  match d:
    case Src.Dir{e, j}:
      json_fits(j)

def mdir_fits(m: Maybe<&2, Src.Dir>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      dir_fits(d)

# every count, number and length of the request fits the wire
def req_fits(f: Src.Facts) -> Bool:
  match f:
    case Src.Facts{b, +ms, rb, m}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ms)), LawsBase.wire_nats_fit(ms)), mdir_fits(m))

# Laws
# ----

# LAW codemode_source_ffi_answers: a spelled request whose numbers fit the wire answers the spelled answer of the model
# EXCLUDES: a fact misread (a flag swapped, a tag off by one, a key or a
#   value lost), an answer spelled with another tag or with its flags
#   swapped
law codemode_source_ffi_answers:
  for +f: Src.Facts
  for h: {req_fits(f) == True{} : Bool}
  {FSrc.ffi(spell_req(f, "")) == spell_reply(f) : String}

# LAW codemode_source_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law codemode_source_ffi_reads:
  for +f: Src.Facts
  for +rest: String
  for h: {req_fits(f) == True{} : Bool}
  {FSrc.get_req(spell_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Src.Facts>}

# LAW codemode_source_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made for input that is no request (an unknown tag,
#   a missing field, a Nat of 15 or more digits, a short string, input
#   left over)
law codemode_source_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSrc.ffi(s)) == False{} : Bool}
  exs f: Src.Facts
  {s == spell_req(f, "") : String} & {req_fits(f) == True{} : Bool}

# LAW codemode_source_ffi_refuses: every error the entry answers is exactly "codemode_source: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law codemode_source_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSrc.ffi(s)) == True{} : Bool}
  {FSrc.ffi(s) == Wr.err("codemode_source: malformed request") : String}

# LAW codemode_source_ffi_example: anchor: the bytes Rust sends and reads: a plain script, split options, a misplaced line, an unknown tag, input left over
# EXCLUDES: another spelling of a fact or an answer
law codemode_source_ffi_example:
  {[FSrc.ffi("F0,F0,"), FSrc.ffi("F0,F1,F2,1,17,max_output_tokens1,5,"), FSrc.ffi("F1,2,F0,"), FSrc.ffi("F0,F2,"), FSrc.ffi("F0,F0,x")] == ["1,", "2,TF", "0,78,The // @options: line must be the first line of the input; found one on line 3", Wr.err("codemode_source: malformed request"), Wr.err("codemode_source: malformed request")] : List<&2, String>}
