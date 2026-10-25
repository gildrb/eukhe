# eukhe: the laws of area error_body

import Base
import ../bend/error_body.bend as Eb
import ../bend/ffi_error_body.bend as FEb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (E1) What a provider's HTTP error shows its user
# ------------------------------------------------
# bend/error_body.bend, run as the compiled core by bend/ffi_error_body.bend
# (eukhe-bend rules/error_body.rs; asked by eukhe-ai utils/error_body.rs for
# every failed provider request). Every input is free: any three probes,
# flag, status, body, prefix, message, text and cap.
#
# R1: the body is the first usable one of three places, in this order:
#     Mistral's `body` when it is a text, `openai`'s `error` when it is an
#     object with a key, Bedrock's `$response.body` when it is a text or
#     such an object. Nothing else is a body (an object in `body`, a text
#     in `error`, a stream, an instance, an empty object).
# R2: the body is trimmed as JS `String.prototype.trim` trims: leading and
#     trailing chars of U+0009..U+000D, U+0020, U+00A0, U+1680,
#     U+2000..U+200A, U+2028, U+2029, U+202F, U+205F, U+3000, U+FEFF go
#     (U+0085 stays); an empty trimmed body is no body.
# R3: a text is cut to a cap of UTF-16 code units (a char past U+FFFF is
#     two): a text within the cap stays; a longer one becomes its longest
#     prefix within the cap that splits no char, then `... [truncated N
#     chars]`, N the units past the cap. The body's cap is 4000.
# R4: the display string: when the message does not carry the body and
#     there is a status and a body, `<prefix> (<status>): <body>`, or
#     `<status>: <body>` without a prefix; otherwise the message, after
#     `<prefix> (<status>): ` when both a prefix and a status are given.
#     The status comes rendered (Rust renders the JSON number as JS does);
#     whether the message carries the body is Rust's substring search.
# R5: the entry answers each request Rust writes (every number and length
#     within the wire) with the answer of R1-R5, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E error_body: malformed request`.

# Spec helpers
# ------------

def sp_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# R2: JS white space and line terminators, as ranges
def sp_ws(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(sp_in(x, 9, 13), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(sp_in(x, 8192, 8202), Bool.or(sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))))))))

# whether every char of s is white space
def sp_all_ws(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sp_ws(c), sp_all_ws(t))

def sp_trim_start.pick(ws: Bool, +c: Char, +t: String, rest: String) -> String:
  match ws:
    case True{}:
      rest
    case False{}:
      SCon{c, t}

# R2: s from its first char that is no white space
def sp_trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sp_trim_start.pick(sp_ws(c), c, t, sp_trim_start(t))

def sp_trim_end.pick(rest_ws: Bool, +c: Char, +t: String, kept: String) -> String:
  match rest_ws:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, kept}

# R2: s up to where only white space is left
def sp_trim_end(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sp_trim_end.pick(sp_all_ws(SCon{c, t}), c, t, sp_trim_end(t))

def sp_trim(s: String) -> String:
  sp_trim_end(sp_trim_start(s))

def sp_u.pick(astral: Bool) -> Nat:
  match astral:
    case True{}:
      2n
    case False{}:
      1n

# R3: the UTF-16 code units of a char
def sp_u(c: Char) -> Nat:
  sp_u.pick(U32.is_lt(65535, Char.to_u32(c)))

# R3: the UTF-16 code units of a text
def sp_units(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      Nat.add(sp_u(c), sp_units(t))

def sp_prefix.pick(fits: Bool, +c: Char, rest: String) -> String:
  match fits:
    case True{}:
      SCon{c, rest}
    case False{}:
      SNil{}

# R3: the longest prefix of s within room units that splits no char
def sp_prefix(s: String, +room: Nat) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sp_prefix.pick(Nat.is_le(sp_u(c), room), c, sp_prefix(t, Nat.sub(room, sp_u(c))))

def sp_truncate.pick(within: Bool, +text: String, +cap: Nat) -> String:
  match within:
    case True{}:
      text
    case False{}:
      String.concat([sp_prefix(text, cap), "... [truncated ", Nat.show(Nat.sub(sp_units(text), cap)), " chars]"])

# R3: text cut to cap units
def sp_truncate(+text: String, +cap: Nat) -> String:
  sp_truncate.pick(Nat.is_le(sp_units(text), cap), text, cap)

def sp_pick.later(e: Eb.Probe, r: Eb.Probe) -> Maybe<&2, String>:
  match e r:
    case Eb.PObj{x} _:
      Some{x}
    case Eb.PNone{} Eb.PText{x}:
      Some{x}
    case Eb.PNone{} Eb.PObj{x}:
      Some{x}
    case Eb.PNone{} Eb.PNone{}:
      None{}
    case Eb.PText{y} Eb.PText{x}:
      Some{x}
    case Eb.PText{y} Eb.PObj{x}:
      Some{x}
    case Eb.PText{y} Eb.PNone{}:
      None{}

# R1: the first usable body: a text in `body`, else an object in `error`,
# else a text or an object in `$response.body`
def sp_pick(b: Eb.Probe, e: Eb.Probe, r: Eb.Probe) -> Maybe<&2, String>:
  match b:
    case Eb.PText{x}:
      Some{x}
    case Eb.PNone{}:
      sp_pick.later(e, r)
    case Eb.PObj{y}:
      sp_pick.later(e, r)

def sp_body.of(empty: Bool, +t: String) -> Maybe<&2, String>:
  match empty:
    case True{}:
      None{}
    case False{}:
      Some{sp_truncate(t, 4000n)}

def sp_body.trim(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      +t = sp_trim(x)
      sp_body.of(String.is_empty(t), t)

# R1-R3: the body
def sp_body(b: Eb.Probe, e: Eb.Probe, r: Eb.Probe) -> Maybe<&2, String>:
  sp_body.trim(sp_pick(b, e, r))

# R4: the display string
def sp_show(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>, p: Maybe<&2, String>, m: String) -> String:
  match c st b p:
    case False{} Some{s} Some{x} Some{q}:
      String.concat([q, " (", s, "): ", x])
    case False{} Some{s} Some{x} None{}:
      String.concat([s, ": ", x])
    case False{} Some{s} None{} Some{q}:
      String.concat([q, " (", s, "): ", m])
    case False{} Some{s} None{} None{}:
      m
    case False{} None{} _ _:
      m
    case True{} Some{s} _ Some{q}:
      String.concat([q, " (", s, "): ", m])
    case True{} Some{s} _ None{}:
      m
    case True{} None{} _ _:
      m

# R5: the spelling of a request and of its reply

def sp_w_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def sp_w_probe(p: Eb.Probe, rest: String) -> String:
  match p:
    case Eb.PNone{}:
      Wr.put_nat(0n, rest)
    case Eb.PText{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case Eb.PObj{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))

def sp_w_req(q: FEb.Req, rest: String) -> String:
  match q:
    case FEb.QBody{b, e, r}:
      Wr.put_nat(0n, sp_w_probe(b, sp_w_probe(e, sp_w_probe(r, rest))))
    case FEb.QShow{c, st, b, p, m}:
      Wr.put_nat(1n, Wr.put_bool(c, sp_w_mstr(st, sp_w_mstr(b, sp_w_mstr(p, Wr.put_str(m, rest))))))
    case FEb.QTruncate{t, cap}:
      Wr.put_nat(2n, Wr.put_str(t, Wr.put_nat(cap, rest)))

def sp_w_reply(q: FEb.Req) -> String:
  match q:
    case FEb.QBody{b, e, r}:
      sp_w_mstr(sp_body(b, e, r), "")
    case FEb.QShow{c, st, b, p, m}:
      Wr.put_str(sp_show(c, st, b, p, m), "")
    case FEb.QTruncate{t, cap}:
      Wr.put_str(sp_truncate(t, cap), "")

def sp_fit_mstr(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(String.length(x))

def sp_fit_probe(p: Eb.Probe) -> Bool:
  match p:
    case Eb.PNone{}:
      True{}
    case Eb.PText{x}:
      LawsBase.wire_fits(String.length(x))
    case Eb.PObj{x}:
      LawsBase.wire_fits(String.length(x))

# every number and length of the request fits the wire
def sp_fit_req(q: FEb.Req) -> Bool:
  match q:
    case FEb.QBody{b, e, r}:
      Bool.and(sp_fit_probe(b), Bool.and(sp_fit_probe(e), sp_fit_probe(r)))
    case FEb.QShow{c, st, b, p, m}:
      Bool.and(sp_fit_mstr(st), Bool.and(sp_fit_mstr(b), Bool.and(sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)))))
    case FEb.QTruncate{t, cap}:
      Bool.and(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(cap))

# Laws: the body and the display string
# -------------------------------------

# LAW error_body_body (R1-R3): the body of every three probes is the
# spec's
# EXCLUDES: the places probed in another order, an object taken from
#   Mistral's `body` or a text from `openai`'s `error`, a stream or an empty
#   object read as a body, U+0085 trimmed or U+FEFF kept, a trim of one end
#   only, an empty body kept, another cap
law error_body_body:
  for +b: Eb.Probe
  for +e: Eb.Probe
  for +r: Eb.Probe
  {Eb.body(b, e, r) == sp_body(b, e, r) : Maybe<&2, String>}

# LAW error_body_truncate (R3): every text cut to every cap is the spec's
# EXCLUDES: chars counted instead of UTF-16 units, a char past U+FFFF split
#   or dropped when it would fit, a cut at the cap minus one, a marker that
#   counts chars or the kept part, a text at the cap marked
law error_body_truncate:
  for +text: String
  for +cap: Nat
  {Eb.truncate(text, cap) == sp_truncate(text, cap) : String}

# LAW error_body_show (R4): the display string of every flag, status, body,
# prefix and message is the spec's
# EXCLUDES: the body shown when the message carries it, the status dropped
#   with a prefix, another separator, the prefix shown without a status
law error_body_show:
  for +c: Bool
  for +st: Maybe<&2, String>
  for +b: Maybe<&2, String>
  for +p: Maybe<&2, String>
  for +m: String
  {Eb.show(c, st, b, p, m) == sp_show(c, st, b, p, m) : String}

# LAW error_body_example (R1-R4): anchor: the shapes of the Rust tests,
# short: Mistral's text body, `openai`'s object, Bedrock's text, a stream
# (no body), an empty object (no body), a body trimmed of U+FEFF but not
# U+0085, a white-space text body (no body, the object after it unread), a cut text, a char past U+FFFF kept whole,
# a carried body, the display strings with and without a prefix
# EXCLUDES: a spec that drifts from the Rust it replaced
law error_body_example:
  {([Eb.body(Eb.PText{" w "}, Eb.PObj{"{x}"}, Eb.PNone{}), Eb.body(Eb.PObj{"{y}"}, Eb.PObj{"{x}"}, Eb.PNone{}), Eb.body(Eb.PNone{}, Eb.PText{"t"}, Eb.PText{"b"}), Eb.body(Eb.PNone{}, Eb.PNone{}, Eb.PNone{}), Eb.body(Eb.PText{SCon{Chr{65279}, SCon{'a', SCon{Chr{133}, SNil{}}}}}, Eb.PNone{}, Eb.PNone{}), Eb.body(Eb.PText{" \n"}, Eb.PObj{"{x}"}, Eb.PNone{})], [Eb.truncate("abcdef", 3n), Eb.truncate("abc", 3n), Eb.truncate(SCon{Chr{128512}, "ab"}, 2n), Eb.truncate(SCon{'a', SCon{Chr{128512}, SNil{}}}, 2n), Eb.show(False{}, Some{"403"}, Some{"x"}, Some{"P"}, "m"), Eb.show(False{}, Some{"403"}, Some{"x"}, None{}, "m"), Eb.show(True{}, Some{"403"}, Some{"x"}, Some{"P"}, "m"), Eb.show(True{}, None{}, None{}, Some{"P"}, "m")]) == ([Some{"w"}, Some{"{x}"}, Some{"b"}, None{}, Some{SCon{'a', SCon{Chr{133}, SNil{}}}}, None{}], ["abc... [truncated 3 chars]", "abc", SCon{Chr{128512}, "... [truncated 2 chars]"}, "a... [truncated 1 chars]", "P (403): x", "403: x", "P (403): m", "m"]) : List<&2, Maybe<&2, String>> & List<&2, String>}

# Laws: the entry (R5)
# --------------------

# LAW error_body_entry_answers (R5): the entry answers every request Rust
# spells, every number and length within the wire, with the spelled answer
# of the spec
# EXCLUDES: the fields read in another order, a probe read as another, a
#   default
law error_body_entry_answers:
  for +q: FEb.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FEb.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW error_body_entry_reads (R5): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law error_body_entry_reads:
  for +q: FEb.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FEb.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEb.Req>}

# LAW error_body_entry_exact (R5): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question or
#   probe, a malformed field, input left over)
law error_body_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FEb.ffi(s)) == False{} : Bool}
  exs r: FEb.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW error_body_entry_refuses (R5): every error the entry answers is
# exactly `E error_body: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law error_body_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FEb.ffi(s)) == True{} : Bool}
  {FEb.ffi(s) == Wr.err("error_body: malformed request") : String}

# LAW error_body_entry_example (R5): anchor: the wire strings Rust sends
# and the replies it reads; an unknown probe, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law error_body_entry_example:
  {[FEb.ffi("0,1,2, 22,3,{a}0,"), FEb.ffi("0,0,2,3,{a}0,"), FEb.ffi("1,F1,3,4031,1,x1,1,P1,m"), FEb.ffi("2,6,abcdef3,"), FEb.ffi("0,3,0,0,"), FEb.ffi("2,1,a3,x")] == ["1,1,2", "1,3,{a}", "10,P (403): x", "26,abc... [truncated 3 chars]", Wr.err("error_body: malformed request"), Wr.err("error_body: malformed request")] : List<&2, String>}
