# eukhe: the spec helpers the laws of two or more areas use

import Base
import ../bend/semver.bend as Sv
import ../bend/staging.bend as Sg
import ../bend/wire.bend as Wr
import ../bend/doc_lines.bend as Dl

# x is written with at most 14 digits
def rank_spec.short(+x: Nat) -> Bool:
  Nat.is_le(List.length(&2, Sv.Dig, Sv.Num.dec(x)), 14n)

# ---- wire ----

# LAWS (the wire format of the compiled Bend core): every entry of
# bend/core.bend reads its input and writes its reply in the format of
# bend/wire.bend (grammar: crates/eukhe-bend/WIRE.md). Each law is an open
# claim about bend/wire.bend; PROOF.bend proves them (as Wire.<law>) with
# the lemmas of proof/wire/.
#
# R1: a decoder reads back what its encoder wrote, and leaves the input
#     after it untouched (so values compose: the laws quantify `rest`).
# R2: a decoder accepts only an encoder's output: any other input is
#     Bad{}, never a default (leading zeros, a missing ',', a short
#     string, a wrong count, an unknown char).
# R3: a Nat has at most 14 digits, decided while reading, so no input can
#     push a Nat past the runtime's 2^48-1 bound; a longer encoding is
#     refused, never misread.
# R4: no encoding starts with 'E', so a reply is either a value or the
#     error form 'E ' + text.

# Spec helpers
# ------------

# 1 + how many more decimal digits follow the lowest one of a value whose
# higher part is q (the fuel f >= q is enough)
def wire_digits.go(f: Nat, q: Nat) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+g:
      match q:
        case 0n:
          0n
        case 1n+p:
          +m = {1n+p : Nat}
          1n+wire_digits.go(g, Nat.div(m, 10n))

# how many decimal digits n has (0 has one)
def wire_digits(n: Nat) -> Nat:
  +m = n
  1n+wire_digits.go(m, Nat.div(m, 10n))

# n fits the wire: at most 14 decimal digits
def wire_fits(n: Nat) -> Bool:
  Nat.is_le(wire_digits(n), 14n)

# every item of xs fits the wire
def wire_nats_fit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(wire_fits(x), wire_nats_fit(t))

# the char of the decimal digit d: the char of code 48 + d (no table)
def wire_dec_char(d: Nat) -> Char:
  Chr{U32.from_nat(Nat.add(48n, d))}

# the decimal digits of n before acc, most significant first, by repeated
# division by 10; none when n is 0 (the caller wrote the lowest digit).
# The fuel f bounds the digits (f >= n is enough).
def wire_dec.go(f: Nat, n: Nat, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+g:
      match n:
        case 0n:
          acc
        case 1n+p:
          +m = {1n+p : Nat}
          wire_dec.go(g, Nat.div(m, 10n), SCon{wire_dec_char(Nat.mod(m, 10n)), acc})

# a Nat on the wire: its decimal digits (0 is "0"), then ',', then rest
def wire_dec(n: Nat, rest: String) -> String:
  +m = n
  wire_dec.go(m, Nat.div(m, 10n), SCon{wire_dec_char(Nat.mod(m, 10n)), SCon{',', rest}})

# s starts with the char 'E' (the error form of a reply)
def wire_opens_err(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, 'E')

# ---- spec spellers ----

# The spellings every entry law (laws/<area>.bend about bend/ffi_<area>.bend)
# builds its requests and replies from. An entry law never uses the
# entry's own encoders (put_req, put_res, put_*): it spells with these and
# the wire primitives Wr.put_nat, Wr.put_str, Wr.put_bool, Wr.err, whose
# round trip and exactness laws/wire.bend pins. A constructor is
# Wr.put_nat(<its tag>, <its fields>); a record is its fields in order; an
# error reply is Wr.err(<text>). Lemmas to call: proof/wire/base/spell.bend
# and the wire laws wire_strs_spells, wire_nats_spells,
# wire_strs_round_trip, wire_strs_exact, wire_strs_decoded_fit.

# the strings of xs, each spelled, then rest
def wire_spell_strs.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, wire_spell_strs.items(t, rest))

# a list of strings: its count, then each string
def wire_spell_strs(+xs: List<&2, String>, rest: String) -> String:
  Wr.put_nat(List.length(&2, String, xs), wire_spell_strs.items(xs, rest))

# the Nats of xs, each spelled, then rest
def wire_spell_nats.items(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_nat(x, wire_spell_nats.items(t, rest))

# a list of Nats: its count, then each Nat
def wire_spell_nats(+xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Nat, xs), wire_spell_nats.items(xs, rest))

# every string of xs is short enough for the wire
def wire_strs_all(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(wire_fits(String.length(x)), wire_strs_all(t))

# a list of strings fits the wire: its count and every string
def wire_strs_fit(+xs: List<&2, String>) -> Bool:
  Bool.and(wire_fits(List.length(&2, String, xs)), wire_strs_all(xs))

# ---- core entries ----

# LAWS: the entries of the compiled Bend core (bend/core.bend) for the
# thinking ladder, the strict plan and the thinking budgets
# (bend/ffi_effort.bend, bend/ffi_infer.bend, bend/ffi_facts.bend). Each law
# is an open claim about those files; PROOF.bend proves them (as
# Effort.<law>, Infer.<law>, Facts.<law>) on the lemmas of proof/wire/.
#
# R1: a request Rust writes (`put_req`, the grammar of the file's header,
#     every Nat and list length within the wire) reads back whole: no field
#     lost, invented, swapped or reordered, and the rest untouched.
# R2: the entry answers that request with the encoding of the model's
#     decision: the Rust rule is the proven model.
# R3: a malformed request, or one with input left over, answers the
#     entry's error form, never a default decision.
# Every input is free: any facts, maps, levels, tools, caps, budgets and
# any text.

# what fits the wire: a Maybe<Nat> whose Nat fits (None always does)
def core_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)

# a content id or a token that fits the wire (None always does)
def wire_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)

# ---- staging and listing ----

# Text spec helpers of laws/staging.bend and laws/listing.bend: names
# compared char by char, a suffix taken off.

# a and b are the same text, char by char
def text_same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(x, y), text_same(u, v))

# the name n is the text s
def text_named(+s: String, n: Sg.Name) -> Bool:
  match n:
    case Sg.Utf{t}:
      text_same(t, s)
    case Sg.Raw{}:
      False{}

# an entry of es has the name s
def text_has_name(+s: String, es: List<&2, Sg.Seen>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Sg.Seen{n, k}:
          Bool.or(text_named(s, n), text_has_name(s, rest))

def text_found(b: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{""}
    case False{}:
      m

def text_cons(c: Char, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{SCon{c, r}}

# s before the suffix p, when s ends with p
def text_unsuffix(+p: String, +s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      text_found(String.is_empty(p), None{})
    case SCon{c, t}:
      text_found(text_same(SCon{c, t}, p), text_cons(c, text_unsuffix(p, t)))

# ---- doc lines projection ----

# The spellings of the projection of a file's lines (bend/doc_lines.bend
# `Proj`) on the wire, from the wire primitives of bend/wire.bend (the
# requests of bend/ffi_doc_lines.bend and bend/ffi_doc_rows.bend carry
# it): End = 0 (LF) | 1 (CRLF); Maybe<End> = 0 | 1 then the End; a line
# is its length, then its Maybe<End>; a projection is its BOM flag, then
# its lines (count first).

def proj_spell_end(e: Dl.End, rest: String) -> String:
  match e:
    case Dl.Lf{}:
      Wr.put_nat(0n, rest)
    case Dl.CrLf{}:
      Wr.put_nat(1n, rest)

def proj_spell_mend(m: Maybe<&2, Dl.End>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{e}:
      Wr.put_nat(1n, proj_spell_end(e, rest))

def proj_spell_line(l: Dl.Line, rest: String) -> String:
  match l:
    case Dl.Line{n, en}:
      Wr.put_nat(n, proj_spell_mend(en, rest))

def proj_spell(p: Dl.Proj, rest: String) -> String:
  match p:
    case Dl.Proj{b, ls}:
      Wr.put_bool(b, Wr.put_list(~Dl.Line, ~proj_spell_line, ls, rest))

def proj_lines_fit(ls: List<&2, Dl.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> rest:
      match l:
        case Dl.Line{+n, en}:
          Bool.and(wire_fits(n), proj_lines_fit(rest))

# every number of a projection fits the wire: its count and each length
def proj_fits(p: Dl.Proj) -> Bool:
  match p:
    case Dl.Proj{b, +ls}:
      Bool.and(wire_fits(List.length(&2, Dl.Line, ls)), proj_lines_fit(ls))
