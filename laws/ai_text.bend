# eukhe: the laws of area ai_text

import Base
import ../bend/ai_text.bend as T
import ../bend/ffi_ai_text.bend as FT
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./model_name.bend as ModelName

# (AI1) The texts the eukhe-ai providers read
# -------------------------------------------
# bend/ai_text.bend, run as the compiled core by bend/ffi_ai_text.bend
# (eukhe-bend rules/ai_text.rs; asked by eukhe-ai api/google_shared.rs,
# api/google_vertex.rs, api/openrouter_images.rs, api/mistral_conversations
# and utils in place of their `regex` patterns). Every id, text, chunk,
# buffer and raw text is free. "p ++ q" is p then q. A digit is 0-9
# (Rust's `\d` takes every Unicode digit: an intended difference). A line
# break is "\r\n", else "\r", else "\n", read in that order at a place: a
# `\r` with a `\n` right after it is the one break "\r\n".
#
# R1: gemini_major(id): id = P ++ D ++ rest, P "gemini-" or "gemini-live-",
#     D one or more digits, rest not beginning with a digit (D is the
#     maximal run): answer D; else none.
# R2: api_version(text): one part of the text split at `/` (the parts
#     between slashes, the first and the last too) is "v" ++ D ++ B, D one
#     or more digits, B empty or "beta" followed by zero or more digits.
# R3: data_url(chunks): the text t the chunks make, read as one, is
#     "data:" ++ M ++ ";base64," ++ D, M one or more chars none of which is
#     `;`, D one or more chars none of which is a line terminator (U+000A,
#     U+000D, U+2028, U+2029): answer the length of M in chars; else none.
# R4: event_boundary(buffer): the boundary is the first place where a line
#     break is followed right away by a second line break: answer its start
#     (the chars before it) and its length (the two breaks together, 2 to 4
#     chars); no such place: none.
# R5: lines(raw): raw split at each line break: the parts between breaks,
#     the first and the last too (a text ending in a break has an empty
#     last part; the empty text is one empty part).
# R6: the entry answers each request Rust writes (bend/ffi_ai_text.bend
#     header: 0 id, 1 text, 2 chunks, 3 buffer, 4 raw; every count and
#     length within the wire) with the model's answer (R1-R5) spelled as the
#     header says, reads exactly the request and nothing after it, and
#     answers any other input (a tag past 4, input left over too) with the
#     exact error form `E ai_text: malformed request`.

# Spec helpers
# ------------

# x is the char of code k
def sp_is(x: Char, k: U32) -> Bool:
  U32.is_eq(Char.to_u32(x), k)

# R1, R2: d is one or more digits
def sp_digs(d: String) -> Bool:
  match d:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(ModelName.sp_digit(x), ModelName.sp_digits(t))

# R1: r does not begin with a digit
def sp_no_dig(r: String) -> Bool:
  match r:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.not(ModelName.sp_digit(x))

# R1: P: "gemini-live-" (live) or "gemini-"
def sp_gem(live: Bool) -> String:
  match live:
    case True{}:
      "gemini-live-"
    case False{}:
      "gemini-"

# R2: a ends with `/` (47); e when a is empty
def sp_last_slash(a: String, e: Bool) -> Bool:
  match a:
    case SNil{}:
      e
    case SCon{x, t}:
      sp_last_slash(t, sp_is(x, 47))

# R2: b is empty or begins with `/`: the part ends where b begins
def sp_part_end(b: String) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{x, t}:
      sp_is(x, 47)

# R2: B: empty (none), or "beta" then e
def sp_beta(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{e}:
      String.append("beta", e)

# R2: e is zero or more digits
def sp_beta_ok(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      ModelName.sp_digits(e)

# R3: the chunks read as one text
def sp_cat(cs: List<&2, String>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case c <> more:
      String.append(c, sp_cat(more))

# R3: `;` (59)
def sp_semi(x: Char) -> Bool:
  sp_is(x, 59)

# R3: a line terminator: U+000A, U+000D, U+2028, U+2029
def sp_lt(+x: Char) -> Bool:
  Bool.or(sp_is(x, 10), Bool.or(sp_is(x, 13), Bool.or(sp_is(x, 8232), sp_is(x, 8233))))

# R3: no char of m is `;`
def sp_no_semi(m: String) -> Bool:
  match m:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(sp_semi(x)), sp_no_semi(t))

# R3: M: one or more chars, none `;`
def sp_mime(m: String) -> Bool:
  match m:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(Bool.not(sp_semi(x)), sp_no_semi(t))

# R3: no char of d is a line terminator
def sp_no_lt(d: String) -> Bool:
  match d:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(sp_lt(x)), sp_no_lt(t))

# R3: D: one or more chars, no line terminator
def sp_body(d: String) -> Bool:
  match d:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(Bool.not(sp_lt(x)), sp_no_lt(t))

# R3: the data URL of mime m and data d
def sp_data(m: String, d: String) -> String:
  String.append("data:", String.append(m, String.append(";base64,", d)))

# R4, R5: `\r` (13), `\n` (10)
def sp_cr(x: Char) -> Bool:
  sp_is(x, 13)

def sp_lf(x: Char) -> Bool:
  sp_is(x, 10)

# R4, R5: the line break of kind j: 0 "\r\n", 1 "\r", 2 (and past) "\n"
def sp_brk(j: Nat) -> String:
  match j:
    case 0n:
      "\r\n"
    case 1n:
      "\r"
    case 2n+k:
      "\n"

# R4, R5: r does not begin with `\n`
def sp_no_lf(r: String) -> Bool:
  match r:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.not(sp_lf(x))

# R4, R5: the break of kind j, r following it, is read whole there: a `\r`
# with a `\n` right after it is the break "\r\n", not "\r"
def sp_whole(j: Nat, r: String) -> Bool:
  match j:
    case 0n:
      True{}
    case 1n:
      sp_no_lf(r)
    case 2n+k:
      True{}

# R4: the two breaks of kinds j1, j2 together: their length
def sp_span_len(j1: Nat, j2: Nat) -> Nat:
  Nat.add(String.length(sp_brk(j1)), String.length(sp_brk(j2)))

# R4: after a `\r`, the char y and w: a `\n` makes the break "\r\n"
def sp_after.lf(lf: Bool, y: Char, w: String) -> Maybe<&2, String>:
  match lf:
    case True{}:
      Some{w}
    case False{}:
      Some{SCon{y, w}}

def sp_after.at(cr: Bool, lf: Bool, t: String) -> Maybe<&2, String>:
  match cr:
    case True{}:
      match t:
        case SNil{}:
          Some{SNil{}}
        case SCon{+y, w}:
          sp_after.lf(sp_lf(y), y, w)
    case False{}:
      match lf:
        case True{}:
          Some{t}
        case False{}:
          None{}

# R4: the text after the line break at the start of u ("\r\n", else "\r",
# else "\n"); none when no break begins u
def sp_after(u: String) -> Maybe<&2, String>:
  match u:
    case SNil{}:
      None{}
    case SCon{+x, t}:
      sp_after.at(sp_cr(x), sp_lf(x), t)

# R4: a line break begins v
def sp_opens(v: String) -> Bool:
  match v:
    case SNil{}:
      False{}
    case SCon{+x, t}:
      Bool.or(sp_cr(x), sp_lf(x))

def sp_bnd_on(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      sp_opens(v)

# R4: a boundary starts at the start of u: a line break, then right away a
# second line break
def sp_bnd_at(u: String) -> Bool:
  sp_bnd_on(sp_after(u))

# R4: no boundary starts at a place of a, t following a
def sp_clear(a: String, +t: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{x, +rest}:
      Bool.and(Bool.not(sp_bnd_at(SCon{x, String.append(rest, t)})), sp_clear(rest, t))

# R5: no char of a is `\r` or `\n`
def sp_plain(a: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{+x, t}:
      Bool.and(Bool.not(Bool.or(sp_cr(x), sp_lf(x))), sp_plain(t))

# R6: the spelling of a request and of its reply

def sp_w_req(q: FT.Req, rest: String) -> String:
  match q:
    case FT.QMajor{x}:
      Wr.put_nat(0n, Wr.put_str(x, rest))
    case FT.QApi{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case FT.QData{cs}:
      Wr.put_nat(2n, LawsBase.wire_spell_strs(cs, rest))
    case FT.QBound{x}:
      Wr.put_nat(3n, Wr.put_str(x, rest))
    case FT.QLines{x}:
      Wr.put_nat(4n, Wr.put_str(x, rest))

def sp_w_mstr(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, ""))

def sp_w_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, ""))

def sp_w_span(m: Maybe<&2, T.Span>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{p}:
      match p:
        case T.Span{i, l}:
          Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(l, "")))

def sp_w_reply(q: FT.Req) -> String:
  match q:
    case FT.QMajor{x}:
      sp_w_mstr(T.gemini_major(x))
    case FT.QApi{x}:
      Wr.put_bool(T.api_version(x), "")
    case FT.QData{cs}:
      sp_w_mnat(T.data_url(cs))
    case FT.QBound{x}:
      sp_w_span(T.event_boundary(x))
    case FT.QLines{x}:
      LawsBase.wire_spell_strs(T.lines(x), "")

# every count and length of a request fits the wire
def sp_fit_req(q: FT.Req) -> Bool:
  match q:
    case FT.QMajor{x}:
      LawsBase.wire_fits(String.length(x))
    case FT.QApi{x}:
      LawsBase.wire_fits(String.length(x))
    case FT.QData{cs}:
      LawsBase.wire_strs_fit(cs)
    case FT.QBound{x}:
      LawsBase.wire_fits(String.length(x))
    case FT.QLines{x}:
      LawsBase.wire_fits(String.length(x))

# Laws: R1, a Gemini id's major version
# -------------------------------------
# old regex, on the lowercased id: ^gemini(?:-live)?-(\d+)

# LAW ai_major_complete (R1): "gemini-" or "gemini-live-", then a maximal
# run of one or more digits, answers that run
# EXCLUDES: the live form refused, a run cut short or read past its end, a
#   digit refused, text after the run that changes the answer
law ai_major_complete:
  for +live: Bool
  for +d: String
  for +rest: String
  for hd: {sp_digs(d) == True{} : Bool}
  for hr: {sp_no_dig(rest) == True{} : Bool}
  {T.gemini_major(String.append(sp_gem(live), String.append(d, rest))) == Some{d} : Maybe<&2, String>}

# LAW ai_major_sound (R1): an id that answers D is "gemini-" or
# "gemini-live-", then D, one or more digits, then text that does not
# begin with a digit
# EXCLUDES: a prefix found past the start, another prefix (gemini_, live-
#   alone), an empty D, a D that is not the whole run, a non-digit in D
law ai_major_sound:
  for +id: String
  for +d: String
  for h: {T.gemini_major(id) == Some{d} : Maybe<&2, String>}
  exs live: Bool
  exs rest: String
  {id == String.append(sp_gem(live), String.append(d, rest)) : String} & ({sp_digs(d) == True{} : Bool} & {sp_no_dig(rest) == True{} : Bool})

# LAW ai_major_example (R1): anchor: hits and misses
# EXCLUDES: a rule that drifts from the regex it replaced
law ai_major_example:
  {[T.gemini_major("gemini-2.5-pro"), T.gemini_major("gemini-live-3x"), T.gemini_major("gemini-x"), T.gemini_major("gemini-12"), T.gemini_major("gemini-live-"), T.gemini_major("gemini2"), T.gemini_major("xgemini-2")] == [Some{"2"}, Some{"3"}, None{}, Some{"12"}, None{}, None{}, None{}] : List<&2, Maybe<&2, String>>}

# Laws: R2, an API version in a path
# ----------------------------------
# old regexes: ^v\d+(?:beta\d*)?$ per path segment, and
# (?:^|/)v\d+(?:beta\d*)?(?:/|$) over the text

# LAW ai_api_complete (R2): a part "v" ++ D ++ B (D one or more digits, B
# empty or "beta" and zero or more digits), anywhere in the text (after
# the start or a `/`, before the end or a `/`), answers True
# EXCLUDES: only the first or the last part read, beta refused, a beta
#   number required, a number of several digits refused
law ai_api_complete:
  for +a: String
  for +d: String
  for +m: Maybe<&2, String>
  for +b: String
  for ha: {sp_last_slash(a, True{}) == True{} : Bool}
  for hd: {sp_digs(d) == True{} : Bool}
  for hm: {sp_beta_ok(m) == True{} : Bool}
  for hb: {sp_part_end(b) == True{} : Bool}
  {T.api_version(String.append(a, String.append("v", String.append(d, String.append(sp_beta(m), b))))) == True{} : Bool}

# LAW ai_api_sound (R2): a text that answers True has such a part, after
# the start or a `/` and before the end or a `/`
# EXCLUDES: a version inside a part (/xv1/, /v1x/), "v" with no digits,
#   "beta" with a non-digit after it, a part ending in another char
law ai_api_sound:
  for +s: String
  for h: {T.api_version(s) == True{} : Bool}
  exs a: String
  exs d: String
  exs m: Maybe<&2, String>
  exs b: String
  {s == String.append(a, String.append("v", String.append(d, String.append(sp_beta(m), b)))) : String} & ({sp_last_slash(a, True{}) == True{} : Bool} & ({sp_digs(d) == True{} : Bool} & ({sp_beta_ok(m) == True{} : Bool} & {sp_part_end(b) == True{} : Bool})))

# LAW ai_api_example (R2): anchor: hits and misses
# EXCLUDES: a rule that drifts from the regexes it replaced
law ai_api_example:
  {[T.api_version("/v1beta/models"), T.api_version("/v1beta2"), T.api_version("/vbeta"), T.api_version("/v1x/"), T.api_version("v2"), T.api_version("a/v1/b"), T.api_version("/v1beta2x"), T.api_version("xv1"), T.api_version("")] == [True{}, True{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}

# Laws: R3, a base64 data URL
# ---------------------------
# old regex: ^data:([^;]+);base64,([^\n\r\u{2028}\u{2029}]+)$

# LAW ai_data_complete (R3): chunks that make "data:" ++ M ++ ";base64,"
# ++ D, however the text is cut, answer the length of M in chars
# EXCLUDES: a chunk read on its own (a border inside the mark), a length in
#   bytes, a mime cut at a char other than `;`, a data char refused
law ai_data_complete:
  for +cs: List<&2, String>
  for +m: String
  for +d: String
  for hc: {sp_cat(cs) == sp_data(m, d) : String}
  for hm: {sp_mime(m) == True{} : Bool}
  for hd: {sp_body(d) == True{} : Bool}
  {T.data_url(cs) == Some{String.length(m)} : Maybe<&2, Nat>}

# LAW ai_data_sound (R3): chunks that answer n make "data:" ++ M ++
# ";base64," ++ D, M of n chars
# EXCLUDES: an empty mime or data, a `;` in the mime, a line terminator in
#   the data, another mark, text before "data:"
law ai_data_sound:
  for +cs: List<&2, String>
  for +n: Nat
  for h: {T.data_url(cs) == Some{n} : Maybe<&2, Nat>}
  exs m: String
  exs d: String
  {sp_cat(cs) == sp_data(m, d) : String} & ({sp_mime(m) == True{} : Bool} & ({sp_body(d) == True{} : Bool} & {String.length(m) == n : Nat}))

# LAW ai_data_example (R3): anchor: hits and misses, one cut into chunks
# EXCLUDES: a rule that drifts from the regex it replaced
law ai_data_example:
  {[T.data_url(["data:image/png;base64,QUJD"]), T.data_url(["data:;base64,QQ"]), T.data_url(["data:a;base64,Q\nQ"]), T.data_url(["da", "ta:a;b", "ase64,", "Q"]), T.data_url(["data:a;base64,"]), T.data_url([]), T.data_url([String.append("data:", SCon{Chr{233}, ";base64,QQ"})]), T.data_url(["data:a;b;base64,Q"]), T.data_url(["xdata:a;base64,Q"]), T.data_url(["data:a;base64,Q\r"]), T.data_url([String.append("data:a;base64,Q", SCon{Chr{8232}, ""})]), T.data_url([String.append("data:a;base64,Q", SCon{Chr{8233}, ""})]), T.data_url([String.append("data:a;base64,Q", SCon{Chr{14}, ""})])] == [Some{9n}, None{}, None{}, Some{1n}, None{}, None{}, Some{1n}, None{}, None{}, None{}, None{}, None{}, Some{1n}] : List<&2, Maybe<&2, Nat>>}

# Laws: R4, the event boundary
# ----------------------------
# old regex (leftmost-first):
# \r\n\r\n|\r\n\r|\r\n\n|\r\r\n|\n\r\n|\r\r|\n\r|\n\n

# LAW ai_boundary_first (R4): two line breaks right after each other, each
# read whole, with no boundary at a place before them, answer their start
# and their length
# EXCLUDES: a later boundary preferred, a "\r\n" read as two breaks, a
#   break cut short (length 3 for 4), a start counted in bytes
law ai_boundary_first:
  for +a: String
  for +j1: Nat
  for +j2: Nat
  for +r: String
  for hw1: {sp_whole(j1, String.append(sp_brk(j2), r)) == True{} : Bool}
  for hw2: {sp_whole(j2, r) == True{} : Bool}
  for ha: {sp_clear(a, String.append(sp_brk(j1), String.append(sp_brk(j2), r))) == True{} : Bool}
  {T.event_boundary(String.append(a, String.append(sp_brk(j1), String.append(sp_brk(j2), r)))) == Some{T.Span{String.length(a), sp_span_len(j1, j2)}} : Maybe<&2, T.Span>}

# LAW ai_boundary_sound (R4): an answer is the start and length of two line
# breaks right after each other, each read whole, with no boundary at a
# place before them
# EXCLUDES: a boundary invented (one break, "\r\n" alone), a later place
#   answered, a length that is not the two breaks
law ai_boundary_sound:
  for +s: String
  for +i: Nat
  for +l: Nat
  for h: {T.event_boundary(s) == Some{T.Span{i, l}} : Maybe<&2, T.Span>}
  exs a: String
  exs j1: Nat
  exs j2: Nat
  exs r: String
  {s == String.append(a, String.append(sp_brk(j1), String.append(sp_brk(j2), r))) : String} & ({sp_whole(j1, String.append(sp_brk(j2), r)) == True{} : Bool} & ({sp_whole(j2, r) == True{} : Bool} & ({sp_clear(a, String.append(sp_brk(j1), String.append(sp_brk(j2), r))) == True{} : Bool} & {(String.length(a), sp_span_len(j1, j2)) == (i, l) : Nat & Nat})))

# LAW ai_boundary_none (R4): a buffer where no boundary starts at any place
# answers none
# EXCLUDES: a boundary invented, a default place
law ai_boundary_none:
  for +s: String
  for h: {sp_clear(s, "") == True{} : Bool}
  {T.event_boundary(s) == None{} : Maybe<&2, T.Span>}

# LAW ai_boundary_example (R4): anchor: hits and misses
# EXCLUDES: a rule that drifts from the regex it replaced
law ai_boundary_example:
  {[T.event_boundary("\r\n\r"), T.event_boundary("\r\n"), T.event_boundary("a\n\r\nb"), T.event_boundary("\r\n\r\n"), T.event_boundary("x\r\ry"), T.event_boundary("\n\n"), T.event_boundary("\r\r\n"), T.event_boundary("a\rb\nc"), T.event_boundary(""), T.event_boundary("x\r")] == [Some{T.Span{0n, 3n}}, None{}, Some{T.Span{1n, 3n}}, Some{T.Span{0n, 4n}}, Some{T.Span{1n, 2n}}, Some{T.Span{0n, 2n}}, Some{T.Span{0n, 3n}}, None{}, None{}, None{}] : List<&2, Maybe<&2, T.Span>>}

# Laws: R5, lines
# ---------------
# old regex: Regex::new(r"\r\n|\r|\n").split(raw)

# LAW ai_lines_break (R5): a part with no break char, then a line break
# read whole, then b: that part, then the lines of b
# EXCLUDES: "\r\n" read as two breaks, a break kept in a part, a part lost
#   or merged with the next, a break char in a part
law ai_lines_break:
  for +a: String
  for +j: Nat
  for +b: String
  for ha: {sp_plain(a) == True{} : Bool}
  for hw: {sp_whole(j, b) == True{} : Bool}
  {T.lines(String.append(a, String.append(sp_brk(j), b))) == a <> T.lines(b) : List<&2, String>}

# LAW ai_lines_plain (R5): a text with no break char is one line, itself
# (the empty text too)
# EXCLUDES: the empty text read as no lines, a last part dropped, a text
#   changed
law ai_lines_plain:
  for +a: String
  for ha: {sp_plain(a) == True{} : Bool}
  {T.lines(a) == [a] : List<&2, String>}

# LAW ai_lines_example (R5): anchor
# EXCLUDES: a split that drifts from the regex it replaced
law ai_lines_example:
  {[T.lines("a\r\nb\rc\n"), T.lines(""), T.lines("\r\r\n"), T.lines("a\n\rb"), T.lines("\r\n\n"), T.lines("\na")] == [["a", "b", "c", ""], [""], ["", "", ""], ["a", "", "b"], ["", "", ""], ["", "a"]] : List<&2, List<&2, String>>}

# Laws: the entry (R6)
# --------------------

# LAW ai_text_entry_decides (R6): a request spelled by the grammar, every
# count and length within the wire, is answered with the spelling of the
# model's answer
# EXCLUDES: a request read as another, a field lost, a reply spelled
#   another way (a missing Maybe tag, start and length swapped, a line lost)
law ai_text_entry_decides:
  for +q: FT.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FT.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW ai_text_entry_left_over (R6): input left over after a spelled
# request answers the malformed error
# EXCLUDES: trailing input ignored, or read as part of the request
law ai_text_entry_left_over:
  for +q: FT.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FT.ffi(sp_w_req(q, rest)) == Wr.err("ai_text: malformed request") : String}

# LAW ai_text_entry_reads_only_requests (R6): an answer that is not the
# error form answers a request: the input is the spelling of a request that
# fits the wire, and the answer is the model's answer to it
# EXCLUDES: a decoder that accepts an unknown tag, a short string, a count
#   past the wire or a missing field, and answers it anyway
law ai_text_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FT.ffi(s)) == False{} : Bool}
  exs q: FT.Req
  {(s, (sp_fit_req(q), FT.ffi(s))) == (sp_w_req(q, ""), (True{}, sp_w_reply(q))) : String & (Bool & String)}

# LAW ai_text_entry_unknown_request (R6): a request tag past 4 is
# malformed, whatever follows
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law ai_text_entry_unknown_request:
  for +n: Nat
  for +rest: String
  {FT.ffi(Wr.put_nat(5n+n, rest)) == Wr.err("ai_text: malformed request") : String}

# LAW ai_text_entry_malformed_unless_request (R6): an input that does not
# begin with a spelled request that fits answers the malformed error
# EXCLUDES: another error text, or a reply, for input that holds no request
law ai_text_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(FT.ffi(s), Wr.err("ai_text: malformed request")) == False{} : Bool}
  exs q: FT.Req
  exs rest: String
  {(s, sp_fit_req(q)) == (sp_w_req(q, rest), True{}) : String & Bool}

# LAW ai_text_entry_example (R6): anchor: the wire strings Rust sends and
# the replies it reads; an unknown request, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law ai_text_entry_example:
  {[FT.ffi("0,14,gemini-2.5-pro"), FT.ffi("0,8,gemini-x"), FT.ffi("1,8,/v1beta2"), FT.ffi("2,2,5,data:11,a;base64,QQ"), FT.ffi("2,1,1,x"), FT.ffi("3,5,a\n\r\nb"), FT.ffi("3,2,\r\n"), FT.ffi("4,4,a\r\nb"), FT.ffi("5,"), FT.ffi("0,1,ab")] == ["1,1,2", "0,", "T", "1,1,", "0,", "1,1,3,", "0,", "2,1,a1,b", Wr.err("ai_text: malformed request"), Wr.err("ai_text: malformed request")] : List<&2, String>}

# LAW ai_text_entry_premises_witness (R6): a request that fits exists, and
# so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law ai_text_entry_premises_witness:
  {(sp_fit_req(FT.QMajor{"x"}), FT.ffi("")) == (True{}, Wr.err("ai_text: malformed request")) : Bool & String}
