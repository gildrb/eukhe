# eukhe: the laws of area codemode_id

import Base
import ../bend/codemode_id.bend as Ci
import ../bend/ffi_codemode_id.bend as FCi
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the identifier a code-mode script uses for a tool
# (bend/codemode_id.bend, the port of pi-codemode `identifier.ts`). Each
# law is an open claim about Ci.of; PROOF.bend proves them (as
# CodemodeId.<law>) with the lemmas of proof/codemode_id/.
#
# R1: a char of the tool's name stays where a JavaScript identifier may
#     hold it, else it becomes `_`: the first char may be an ASCII letter
#     (A-Z, a-z), `_` or `$`; every later char also an ASCII digit (0-9).
#     A char is a code point: one char past ASCII is one `_`. The name ""
#     is `_`. A text is an identifier when every char stands where it may
#     (Ci.test). Every name is free: any chars, any length.

# Terms
# -----

# x is the code of an ASCII letter: A-Z (65-90) or a-z (97-122)
def letter_spec(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), Bool.and(U32.is_le(97, x), U32.is_le(x, 122)))

# x is the code of an ASCII digit 0-9 (48-57)
def digit_spec(+x: U32) -> Bool:
  Bool.and(U32.is_le(48, x), U32.is_le(x, 57))

# x is the code of `_` (95) or `$` (36)
def mark_spec(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 36))

# a JavaScript identifier may hold the char of code x at its start (first
# True) or after it: a letter, `_` or `$` anywhere, a digit only after the
# start
def ok_spec(first: Bool, +x: U32) -> Bool:
  Bool.or(Bool.or(letter_spec(x), mark_spec(x)), Bool.and(Bool.not(first), digit_spec(x)))

def fix_spec(ok: Bool, c: Char) -> Char:
  match ok:
    case True{}:
      c
    case False{}:
      '_'

# what a name ends as: `_` when no char was read (first), else nothing
def end_spec(first: Bool) -> String:
  match first:
    case True{}:
      "_"
    case False{}:
      ""

# the identifier of s, one loop: each char kept where it may stand, else
# `_`; first: no char read yet, so an empty name gives `_`
def id_spec.go(s: String, first: Bool) -> String:
  match s:
    case SNil{}:
      end_spec(first)
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          SCon{fix_spec(ok_spec(first, x), Chr{x}), id_spec.go(t, False{})}

def id_spec(s: String) -> String:
  id_spec.go(s, True{})

# every char of s may stand after the start of an identifier
def parts_spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.and(ok_spec(False{}, x), parts_spec(t))

# s is a JavaScript identifier of ASCII chars: not empty, its first char
# may start one, every later char may continue one
def ident_spec(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.and(ok_spec(True{}, x), parts_spec(t))

# the text of a request fits the wire
def req_fits(q: FCi.Req) -> Bool:
  match q:
    case FCi.QId{n}:
      LawsBase.wire_fits(String.length(n))
    case FCi.QIs{n}:
      LawsBase.wire_fits(String.length(n))

# Laws
# ----

# LAW codemode_id_exact: the identifier of a name is the name with each char a JavaScript identifier may not hold at its place (first: letter, `_`, `$`; later: also a digit) replaced by `_`; the empty name is `_`
# EXCLUDES: a digit kept at the start or replaced later, a non-ASCII
#   letter kept, `$` or `_` replaced, a char dropped or added (one `_` per
#   code point, not per UTF-16 unit or byte), another fill char, an empty
#   identifier
law codemode_id_exact:
  for s: String
  {Ci.of(s) == id_spec(s) : String}

# LAW codemode_id_is_identifier: every identifier is a JavaScript identifier of ASCII chars
# EXCLUDES: an identifier a script cannot name (empty, digit first, a
#   non-ASCII or punctuation char)
law codemode_id_is_identifier:
  for s: String
  {ident_spec(Ci.of(s)) == True{} : Bool}

# LAW codemode_id_keeps_identifiers: a name that is already an identifier is its own identifier
# EXCLUDES: a rename of a valid name (case folding, a prefix, a mangled
#   `mcp__docs__search`): scripts call tools by their names where they can
law codemode_id_keeps_identifiers:
  for +s: String
  for ok: {ident_spec(s) == True{} : Bool}
  {Ci.of(s) == s : String}

# LAW codemode_id_example: anchor: the cases of identifier.ts's port
# EXCLUDES: a spec that is wrong on the shipped examples
law codemode_id_example:
  {Ci.of("mcp__docs__search") == "mcp__docs__search" : String} &
  {Ci.of("$x_1") == "$x_1" : String} &
  {Ci.of("my-tool") == "my_tool" : String} &
  {Ci.of("1st.tool") == "_st_tool" : String} &
  {Ci.of("a😀b") == "a_b" : String} &
  {Ci.of("é") == "_" : String} &
  {Ci.of("") == "_" : String}

# LAW codemode_id_is_exact: a text is an identifier exactly when it is a JavaScript identifier of ASCII chars
# EXCLUDES: the empty text, a digit first, a non-ASCII letter or other
#   punctuation accepted; a valid name refused (a bare object key quoted,
#   a valid global refused)
law codemode_id_is_exact:
  for s: String
  {Ci.test(s) == ident_spec(s) : Bool}

# LAW codemode_id_is_example: anchor: the global names and keys of code mode
# EXCLUDES: a spec that is wrong on real names
law codemode_id_is_example:
  {Ci.test("tools") == True{} : Bool} &
  {Ci.test("$x_1") == True{} : Bool} &
  {Ci.test("my-tool") == False{} : Bool} &
  {Ci.test("1st") == False{} : Bool} &
  {Ci.test("é") == False{} : Bool} &
  {Ci.test("") == False{} : Bool}

# LAWS (R2): the entry of the compiled Bend core that runs the rule
# (bend/ffi_codemode_id.bend, called by crates/eukhe-durable codemode
# through `eukhe_bend::rules::codemode_id`). Each law is an open claim
# about FCi.ffi, the function the core runs, stated with spec spellers
# built only from the wire primitives of bend/wire.bend (their round
# trips: laws/wire.bend).
#
# R2: a request is a question: tag 0 and a tool's name (a String), which
#     the entry answers with its identifier (a String); tag 1 and a text
#     (a String), which it answers with whether the text is an identifier
#     (a Bool). A malformed request answers the error form "codemode_id:
#     malformed request", input left after the request "codemode_id:
#     input left after the request", never a default.

# the identifier question: tag 0, the name, then rest
def spell_id(name: String, rest: String) -> String:
  Wr.put_nat(0n, Wr.put_str(name, rest))

# the identifier test: tag 1, the text, then rest
def spell_is(text: String, rest: String) -> String:
  Wr.put_nat(1n, Wr.put_str(text, rest))

# a request, then rest
def spell_req(q: FCi.Req, rest: String) -> String:
  match q:
    case FCi.QId{n}:
      spell_id(n, rest)
    case FCi.QIs{n}:
      spell_is(n, rest)

# LAW codemode_id_ffi_answers: an identifier question of a name that fits the wire answers that name's identifier
# EXCLUDES: a field misread, another identifier, a reply in another
#   spelling, the two questions swapped
law codemode_id_ffi_answers:
  for +name: String
  for fit: {LawsBase.wire_fits(String.length(name)) == True{} : Bool}
  {FCi.ffi(spell_id(name, "")) == Wr.put_str(id_spec(name), "") : String}

# LAW codemode_id_ffi_is: an identifier test of a text that fits the wire answers whether it is an identifier
# EXCLUDES: a field misread, another answer, the two questions swapped
law codemode_id_ffi_is:
  for +text: String
  for fit: {LawsBase.wire_fits(String.length(text)) == True{} : Bool}
  {FCi.ffi(spell_is(text, "")) == Wr.put_bool(ident_spec(text), "") : String}

# LAW codemode_id_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request
# EXCLUDES: a default answer for a malformed request (an unknown tag, a
#   short text) or one with input left over
law codemode_id_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCi.ffi(s)) == False{} : Bool}
  exs q: FCi.Req
  {s == spell_req(q, "") : String}

# the request decoder fails on s: a bad tag or text
def bad_spec.str(r: Wr.Dec<String>) -> Bool:
  match r:
    case Wr.Got{x, s}:
      False{}
    case Wr.Bad{}:
      True{}

def bad_spec.tag(t: Nat, s: String) -> Bool:
  match t:
    case 0n:
      bad_spec.str(Wr.get_str(s))
    case 1n:
      bad_spec.str(Wr.get_str(s))
    case 2n+u:
      True{}

def bad_spec(r: Wr.Dec<Nat>) -> Bool:
  match r:
    case Wr.Got{t, s}:
      bad_spec.tag(t, s)
    case Wr.Bad{}:
      True{}

# LAW codemode_id_ffi_malformed: an input whose tag is no question, or whose text is no encoding, answers the malformed error form
# EXCLUDES: another error text, a default answer
law codemode_id_ffi_malformed:
  for +s: String
  for bad: {bad_spec(Wr.get_nat(s)) == True{} : Bool}
  {FCi.ffi(s) == Wr.err("codemode_id: malformed request") : String}

# LAW codemode_id_ffi_left_over: a request followed by more input answers the left-over error form
# EXCLUDES: the input after the request ignored or read as part of the
#   text
law codemode_id_ffi_left_over:
  for +q: FCi.Req
  for +c: Char
  for +t: String
  for fit: {req_fits(q) == True{} : Bool}
  {FCi.ffi(spell_req(q, SCon{c, t})) == Wr.err("codemode_id: input left after the request") : String}

# LAW codemode_id_ffi_example: anchor: the exact bytes Rust sends for my-tool and for "", the test of my_tool, and two refusals
# EXCLUDES: another spelling of a request or of a reply
law codemode_id_ffi_example:
  {FCi.ffi("0,7,my-tool") == "7,my_tool" : String} &
  {FCi.ffi("0,0,") == "1,_" : String} &
  {FCi.ffi("1,7,my_tool") == "T" : String} &
  {FCi.ffi("2,7,my-tool") == Wr.err("codemode_id: malformed request") : String} &
  {FCi.ffi("0,1,ab") == Wr.err("codemode_id: input left after the request") : String}
