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

# R2: the chars JS `String.prototype.trim` drops (ECMA-262
# TrimString: WhiteSpace U+0009, U+000B, U+000C, U+FEFF and the Unicode
# Zs chars U+0020, U+00A0, U+1680, U+2000..U+200A, U+202F, U+205F,
# U+3000; LineTerminator U+000A, U+000D, U+2028, U+2029), as ranges
def sp_ws(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(sp_in(x, 9, 13), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(sp_in(x, 8192, 8202), Bool.or(sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))))))))

# R2: every char of s is white space (the empty text too)
def sp_all_ws(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sp_ws(c), sp_all_ws(t))

# R2: the last char of the text c then t is white space
def sp_ends_ws(t: String, c: Char) -> Bool:
  match t:
    case SNil{}:
      sp_ws(c)
    case SCon{d, u}:
      sp_ends_ws(u, d)

# R2: t is what trim keeps of a text with some char that is no white
# space: not empty, its first and its last char no white space
def sp_solid(t: String) -> Bool:
  match t:
    case SNil{}:
      False{}
    case SCon{+c, +u}:
      Bool.and(Bool.not(sp_ws(c)), Bool.not(sp_ends_ws(u, c)))

def sp_pairs.at(astral: Bool, n: Nat) -> Nat:
  match astral:
    case True{}:
      1n+n
    case False{}:
      n

# R3: the chars of s past U+FFFF (each a surrogate pair in UTF-16)
def sp_pairs(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      sp_pairs.at(U32.is_lt(65535, Char.to_u32(c)), sp_pairs(t))

# R3: JS `length` of s: one UTF-16 code unit per char, one more per char
# past U+FFFF
def sp_units(+s: String) -> Nat:
  Nat.add(String.length(s), sp_pairs(s))

def sp_text(p: Eb.Probe) -> Maybe<&2, String>:
  match p:
    case Eb.PText{x}:
      Some{x}
    case Eb.PNone{}:
      None{}
    case Eb.PObj{x}:
      None{}

def sp_object(p: Eb.Probe) -> Maybe<&2, String>:
  match p:
    case Eb.PObj{x}:
      Some{x}
    case Eb.PNone{}:
      None{}
    case Eb.PText{x}:
      None{}

def sp_any(p: Eb.Probe) -> Maybe<&2, String>:
  match p:
    case Eb.PText{x}:
      Some{x}
    case Eb.PObj{x}:
      Some{x}
    case Eb.PNone{}:
      None{}

# the first place of the list that holds something
def sp_first(ms: List<&2, Maybe<&2, String>>) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      match m:
        case Some{x}:
          Some{x}
        case None{}:
          sp_first(t)

# R1: what each place offers as a body, in the order they are probed:
# Mistral's `body` as a text, `openai`'s `error` as an object, Bedrock's
# `$response.body` as either
def sp_places(b: Eb.Probe, e: Eb.Probe, r: Eb.Probe) -> List<&2, Maybe<&2, String>>:
  [sp_text(b), sp_object(e), sp_any(r)]

# R1: the body shown for the text x found first (the body of that text
# alone), none when no place holds one
def sp_body_of(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Eb.body(Eb.PText{x}, Eb.PNone{}, Eb.PNone{})

# R4: the status with the prefix before it: `<prefix> (<status>)`, or the
# status alone
def sp_label(p: Maybe<&2, String>, s: String) -> String:
  match p:
    case Some{q}:
      String.concat([q, " (", s, ")"])
    case None{}:
      s

# R4: the display string shows the body: the message does not carry it,
# and both a status and a body are given
def sp_shows_body(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match c st b:
    case False{} Some{s} Some{x}:
      True{}
    case False{} Some{s} None{}:
      False{}
    case False{} None{} _:
      False{}
    case True{} _ _:
      False{}

# R4: what stands before the message: `<prefix> (<status>): ` when both
# are given, else nothing
def sp_lead(p: Maybe<&2, String>, st: Maybe<&2, String>) -> String:
  match p st:
    case Some{q} Some{s}:
      String.concat([q, " (", s, "): "])
    case Some{q} None{}:
      ""
    case None{} _:
      ""

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

# R5: the reply of a request: the model's answer (bend/error_body.bend,
# pinned by the laws above), spelled
def sp_w_reply(q: FEb.Req) -> String:
  match q:
    case FEb.QBody{b, e, r}:
      sp_w_mstr(Eb.body(b, e, r), "")
    case FEb.QShow{c, st, b, p, m}:
      Wr.put_str(Eb.show(c, st, b, p, m), "")
    case FEb.QTruncate{t, cap}:
      Wr.put_str(Eb.truncate(t, cap), "")

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

# LAW error_body_first (R1): the body of every three probes is the body
# of the first place's text, in the order Mistral's `body` (only a text),
# `openai`'s `error` (only an object), Bedrock's `$response.body` (a text
# or an object), the body of that text alone; none when no place holds
# one. A place found first is the body's source even when it trims to
# nothing (no later place is read)
# EXCLUDES: the places probed in another order, an object taken from
#   Mistral's `body` or a text from `openai`'s `error`, a stream or an empty
#   object read as a body, a later place read after a blank first one
law error_body_first:
  for +b: Eb.Probe
  for +e: Eb.Probe
  for +r: Eb.Probe
  {Eb.body(b, e, r) == sp_body_of(sp_first(sp_places(b, e, r))) : Maybe<&2, String>}

# LAW error_body_trimmed (R2, R3): a text t with no white space at either
# end (and not empty), with any white space p before it and q after it
# (ECMA-262 TrimString's set, sp_ws), has the body t cut to 4000 UTF-16
# units (Eb.truncate, pinned by error_body_cut_within/_over)
# EXCLUDES: U+0085 trimmed or U+FEFF, U+2028, U+3000 kept, a trim of one
#   end only, a char inside the text dropped, another cap
law error_body_trimmed:
  for +p: String
  for +t: String
  for +q: String
  for hp: {sp_all_ws(p) == True{} : Bool}
  for hq: {sp_all_ws(q) == True{} : Bool}
  for ht: {sp_solid(t) == True{} : Bool}
  {Eb.body(Eb.PText{String.append(p, String.append(t, q))}, Eb.PNone{}, Eb.PNone{}) == Some{Eb.truncate(t, 4000n)} : Maybe<&2, String>}

# LAW error_body_blank (R2): a text of white space only (the empty text
# too) is no body
# EXCLUDES: an empty or blank body shown
law error_body_blank:
  for +x: String
  for hx: {sp_all_ws(x) == True{} : Bool}
  {Eb.body(Eb.PText{x}, Eb.PNone{}, Eb.PNone{}) == None{} : Maybe<&2, String>}

# LAW error_body_cut_within (R3): a text of at most cap UTF-16 code units
# (JS `length`: a char past U+FFFF counts two) stays whole, for every cap
# EXCLUDES: a text at the cap marked, chars counted as more units than JS
#   counts
law error_body_cut_within:
  for +text: String
  for +cap: Nat
  for h: {Nat.is_le(sp_units(text), cap) == True{} : Bool}
  {Eb.truncate(text, cap) == text : String}

# LAW error_body_cut_over (R3): a text kept, then a char c, then rest,
# where kept is within cap UTF-16 units and kept then c is past it (so
# kept is the longest prefix within the cap that splits no char), is cut
# to kept then `... [truncated N chars]`, N the units of the whole text
# past the cap
# EXCLUDES: chars counted instead of UTF-16 units, a char past U+FFFF split
#   or dropped when it would fit, a cut at the cap minus one, a marker that
#   counts chars or the kept part
law error_body_cut_over:
  for +kept: String
  for +c: Char
  for +rest: String
  for +cap: Nat
  for hk: {Nat.is_le(sp_units(kept), cap) == True{} : Bool}
  for hc: {Nat.is_lt(cap, sp_units(String.append(kept, SCon{c, SNil{}}))) == True{} : Bool}
  {Eb.truncate(String.append(kept, SCon{c, rest}), cap) == String.concat([kept, "... [truncated ", Nat.show(Nat.sub(sp_units(String.append(kept, SCon{c, rest})), cap)), " chars]"]) : String}

# LAW error_body_show_body (R4): when the message does not carry the body
# and a status s and a body x are given, the display string is
# `<prefix> (<s>): <x>`, or `<s>: <x>` without a prefix
# EXCLUDES: the status dropped with a prefix, another separator, the
#   message shown instead of the body
law error_body_show_body:
  for +s: String
  for +x: String
  for +p: Maybe<&2, String>
  for +m: String
  {Eb.show(False{}, Some{s}, Some{x}, p, m) == String.concat([sp_label(p, s), ": ", x]) : String}

# LAW error_body_show_message (R4): otherwise (the message carries the
# body, or no status, or no body) the display string is the message,
# after `<prefix> (<status>): ` when both a prefix and a status are given
# EXCLUDES: the body shown when the message carries it, the prefix shown
#   without a status, the status dropped with a prefix, the message changed
law error_body_show_message:
  for +c: Bool
  for +st: Maybe<&2, String>
  for +b: Maybe<&2, String>
  for +p: Maybe<&2, String>
  for +m: String
  for h: {sp_shows_body(c, st, b) == False{} : Bool}
  {Eb.show(c, st, b, p, m) == String.append(sp_lead(p, st), m) : String}

# LAW error_body_example (R1-R4): anchor: the shapes of the Rust tests,
# short: Mistral's text body, `openai`'s object, Bedrock's text, a stream
# (no body), an empty object (no body), a body trimmed of U+FEFF but not
# U+0085, a white-space text body (no body, the object after it unread), a
# cut text, a char past U+FFFF kept whole, a carried body, the display
# strings with and without a prefix
# EXCLUDES: a spec that drifts from the Rust it replaced
law error_body_example:
  {([Eb.body(Eb.PText{" w "}, Eb.PObj{"{x}"}, Eb.PNone{}), Eb.body(Eb.PObj{"{y}"}, Eb.PObj{"{x}"}, Eb.PNone{}), Eb.body(Eb.PNone{}, Eb.PText{"t"}, Eb.PText{"b"}), Eb.body(Eb.PNone{}, Eb.PNone{}, Eb.PNone{}), Eb.body(Eb.PText{SCon{Chr{65279}, SCon{'a', SCon{Chr{133}, SNil{}}}}}, Eb.PNone{}, Eb.PNone{}), Eb.body(Eb.PText{" \n"}, Eb.PObj{"{x}"}, Eb.PNone{})], [Eb.truncate("abcdef", 3n), Eb.truncate("abc", 3n), Eb.truncate(SCon{Chr{128512}, "ab"}, 2n), Eb.truncate(SCon{'a', SCon{Chr{128512}, SNil{}}}, 2n), Eb.show(False{}, Some{"403"}, Some{"x"}, Some{"P"}, "m"), Eb.show(False{}, Some{"403"}, Some{"x"}, None{}, "m"), Eb.show(True{}, Some{"403"}, Some{"x"}, Some{"P"}, "m"), Eb.show(True{}, None{}, None{}, Some{"P"}, "m")]) == ([Some{"w"}, Some{"{x}"}, Some{"b"}, None{}, Some{SCon{'a', SCon{Chr{133}, SNil{}}}}, None{}], ["abc... [truncated 3 chars]", "abc", SCon{Chr{128512}, "... [truncated 2 chars]"}, "a... [truncated 1 chars]", "P (403): x", "403: x", "P (403): m", "m"]) : List<&2, Maybe<&2, String>> & List<&2, String>}

# Laws: the entry (R5)
# --------------------

# LAW error_body_entry_answers (R5): the entry answers every request Rust
# spells, every number and length within the wire, with the model's answer
# spelled (the body, the display string or the cut of bend/error_body.bend,
# whose answers error_body_first/_trimmed/_blank/_cut_*/_show_* pin)
# EXCLUDES: the fields read in another order, a probe read as another, a
#   question answered with another one's answer, a default
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
