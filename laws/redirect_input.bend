# eukhe: the laws of area redirect_input

import Base
import ../bend/redirect_input.bend as Ri
import ../bend/ffi_redirect_input.bend as FRi
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) The pasted authorization input of the localhost-callback logins
# ---------------------------------------------------------------------
# bend/redirect_input.bend, run as the compiled core by
# bend/ffi_redirect_input.bend (eukhe-bend rules/redirect_input.rs; asked by
# eukhe-core auth/redirect_input.rs for the subscription and MCP logins'
# paste prompt, the localhost callback, and the Prime Inference key paste).
# Every input is free: any text, code, state and failure.
#
# R1: the cleaned paste (Rust `clean_paste`): every char that is whitespace
#     (Rust `char::is_whitespace`: ri_space) or one of U+200B, U+200C,
#     U+200D, U+2060, U+FEFF dropped, then every leading and every trailing
#     char of `"` `'` `` ` `` `<` `>` U+201C U+201D U+2018 U+2019 trimmed.
# R2: a paste's answer (Rust `parse_redirect_input`) of the cleaned text v:
#     with a `?` in v, the parameters of the text after the first `?` up to
#     its first `#` with its trailing `/`s dropped, then of the text after
#     that `#` (none: empty); else with a `://` in v, the parameters of the
#     text after the first `#` after the first `://` (none: empty); else,
#     h the text before the first `#` (none: all of v) and f the text after
#     it (none: empty): when a `&`-separated piece of h has a `=` and the
#     text before its first `=` is `code`, `state` or `error`, the
#     parameters of h with its trailing `/`s dropped; else when such a
#     piece is in f, the parameters of f; else no code when h is empty;
#     else h is the code and f, when not empty, the state.
# R3: the parameters of carriers (Rust form_urlencoded::parse): each
#     carrier's `&`-separated pieces, empty ones skipped, the name before the
#     piece's first `=` and the value after it (no `=`: empty value), both
#     decoded: `+` is a space; `%` and two ASCII hex digits (either case) a
#     byte, any other `%` itself; the bytes (a char's own UTF-8 bytes, the
#     escaped ones) read as UTF-8 with each maximal invalid part (Unicode
#     "maximal subpart") one U+FFFD (Rust `String::from_utf8_lossy`). A
#     name's value: in the first carrier holding a piece of that name with a
#     non-empty value, the first such value. An `error` value answers the
#     provider failure with the `error_description` value; else a `code`
#     value answers it with the `state` value; else no code.
# R4: the state check (Rust `verify_state`): a paste without a state takes
#     the login's; one with the login's state keeps it; any other state is a
#     mismatch.
# R5: the texts (Rust `RedirectInputError` Display, `exchange_retry_notice`):
#     no code `That address has no authorization code. Paste the full
#     address of the page your browser ended on.`; a mismatch `That address
#     is from a different login attempt (state mismatch). Paste the address
#     from the browser tab this login opened.`; a provider failure `The
#     sign-in page reported an error: <error>` then ` (<description>)` when
#     there is one, then `. Open the login link again and sign in, then
#     paste the new address.`; the notice `Login did not complete: <reason>.
#     Paste the address again, or open the login link again and sign in.`,
#     the reason the error text trimmed of whitespace (R1's set) at both
#     ends, then of its trailing `.`s.
# R6: the entry answers each request Rust writes (tag 0 clean, 1 parse, 4
#     notice: the text; tag 2 verify: the code, the state as Maybe<String>,
#     the login's state; tag 3 text: the failure: 0 no code | 1 mismatch |
#     2 provider: the error and the description as Maybe<String>; every
#     length within the wire) with the model's answer (Ri.clean, Ri.parse,
#     Ri.verify, Ri.text, Ri.notice, which the laws of R1-R5 pin; clean,
#     text, notice: the text; parse, verify: 0 pasted: the code and the
#     state as Maybe<String> | 1 failed: the failure), reads exactly the
#     request and
#     nothing after it, and answers any other input with the exact error
#     form `E redirect_input: malformed request`.

# Spec helpers
# ------------

# x is one of xs
def ri_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), ri_in(x, rest))

# R1: Rust's whitespace (`char::is_whitespace`: Unicode White_Space), by
# code point (the Unicode table, PropList.txt)
def ri_ws() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

# R1: c is whitespace
def ri_space(c: Char) -> Bool:
  ri_in(Char.to_u32(c), ri_ws())

# R1: c is one of U+200B, U+200C, U+200D, U+2060, U+FEFF
def ri_zero_width(c: Char) -> Bool:
  ri_in(Char.to_u32(c), [8203, 8204, 8205, 8288, 65279])

# R1: c is a wrapping char: " ' ` < > U+201C U+201D U+2018 U+2019
def ri_wrapper(c: Char) -> Bool:
  ri_in(Char.to_u32(c), [34, 39, 96, 60, 62, 8220, 8221, 8216, 8217])

# R1: c is dropped anywhere: whitespace or zero-width
def ri_noise(+c: Char) -> Bool:
  Bool.or(ri_space(c), ri_zero_width(c))

# R1: no char of s is dropped anywhere
def ri_quiet(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(ri_noise(c)), ri_quiet(t))

# R1: the first char of s is a wrapping char (none for the empty text)
def ri_wrap_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      ri_wrapper(c)

# R2, R3: the chars that shape a paste: % + & = # ? /
def ri_marks() -> List<&2, U32>:
  [37, 43, 38, 61, 35, 63, 47]

# R2, R3: a char a value may hold as it is: no whitespace or zero-width
# char, no wrapping char, none of % + & = # ? /
def ri_plain_char(+c: Char) -> Bool:
  Bool.not(Bool.or(ri_noise(c), Bool.or(ri_wrapper(c), ri_in(Char.to_u32(c), ri_marks()))))

def ri_plain(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ri_plain_char(c), ri_plain(t))

# R2, R3: a value as Rust's tests generate it (URL-safe tokens): one or
# more plain chars
def ri_value(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      ri_plain(SCon{c, t})

# R2: s holds no char of code x
def ri_lacks(s: String, +x: U32) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(U32.is_eq(Char.to_u32(c), x)), ri_lacks(t, x))

# R2: n slashes
def ri_slashes(n: Nat) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+m:
      SCon{'/', ri_slashes(m)}

# R5: every char of s is whitespace
def ri_spaces(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ri_space(c), ri_spaces(t))

# R5: every char of s is a `.`
def ri_dots(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_eq(c, '.'), ri_dots(t))

# R5: the first char of s is whitespace (none for the empty text)
def ri_space_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      ri_space(c)

# R5: the first char of s is a `.` (none for the empty text)
def ri_dot_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '.')

# R5: the notice of a reason r, Rust's exchange_retry_notice format
# (aeabc30d3^:crates/eukhe-core/src/auth/redirect_input.rs:202-208)
def ri_notice_of(r: String) -> String:
  String.append("Login did not complete: ", String.append(r, ". Paste the address again, or open the login link again and sign in."))

# R6: the spelling of a request and of its reply

def ri_w_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def ri_w_fail(f: Ri.Fail, rest: String) -> String:
  match f:
    case Ri.FMissing{}:
      Wr.put_nat(0n, rest)
    case Ri.FMismatch{}:
      Wr.put_nat(1n, rest)
    case Ri.FProvider{e, d}:
      Wr.put_nat(2n, Wr.put_str(e, ri_w_ms(d, rest)))

def ri_w_answer(a: Ri.Answer) -> String:
  match a:
    case Ri.Pasted{c, m}:
      Wr.put_nat(0n, Wr.put_str(c, ri_w_ms(m, "")))
    case Ri.Failed{f}:
      Wr.put_nat(1n, ri_w_fail(f, ""))

def ri_w_req(q: FRi.Req, rest: String) -> String:
  match q:
    case FRi.QClean{x}:
      Wr.put_nat(0n, Wr.put_str(x, rest))
    case FRi.QParse{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case FRi.QVerify{c, m, e}:
      Wr.put_nat(2n, Wr.put_str(c, ri_w_ms(m, Wr.put_str(e, rest))))
    case FRi.QText{f}:
      Wr.put_nat(3n, ri_w_fail(f, rest))
    case FRi.QNotice{x}:
      Wr.put_nat(4n, Wr.put_str(x, rest))

# the model's answer to q, spelled (R1-R5 pin the model's answers)
def ri_w_reply(q: FRi.Req) -> String:
  match q:
    case FRi.QClean{x}:
      Wr.put_str(Ri.clean(x), "")
    case FRi.QParse{x}:
      ri_w_answer(Ri.parse(x))
    case FRi.QVerify{c, m, e}:
      ri_w_answer(Ri.verify(c, m, e))
    case FRi.QText{f}:
      Wr.put_str(Ri.text(f), "")
    case FRi.QNotice{x}:
      Wr.put_str(Ri.notice(x), "")

def ri_fit_str(s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

def ri_fit_ms(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      ri_fit_str(x)

def ri_fit_fail(f: Ri.Fail) -> Bool:
  match f:
    case Ri.FMissing{}:
      True{}
    case Ri.FMismatch{}:
      True{}
    case Ri.FProvider{e, d}:
      Bool.and(ri_fit_str(e), ri_fit_ms(d))

# every length of the request fits the wire
def ri_fit_req(q: FRi.Req) -> Bool:
  match q:
    case FRi.QClean{x}:
      ri_fit_str(x)
    case FRi.QParse{x}:
      ri_fit_str(x)
    case FRi.QVerify{c, m, e}:
      Bool.and(ri_fit_str(c), Bool.and(ri_fit_ms(m), ri_fit_str(e)))
    case FRi.QText{f}:
      ri_fit_fail(f)
    case FRi.QNotice{x}:
      ri_fit_str(x)

# Laws: the cleaned paste (R1)
# ----------------------------
# These four fix Ri.clean on every text: drop the noise chars one by one,
# then the wrapping chars at either end one by one, until the text is
# empty or neither starts nor ends with one; such a text is kept.

# LAW redirect_input_clean_drops_noise (R1): a whitespace or zero-width char anywhere (the text a, the char x, the text b) changes nothing: the paste cleans as a then b
# EXCLUDES: a whitespace or zero-width char kept, a line break inside a
#   wrapped copy kept, a char next to it dropped too, another whitespace set
law redirect_input_clean_drops_noise:
  for +a: String
  for +x: Char
  for +b: String
  for noise: {ri_noise(x) == True{} : Bool}
  {Ri.clean(String.append(a, SCon{x, b})) == Ri.clean(String.append(a, b)) : String}

# LAW redirect_input_clean_trims_lead (R1): a wrapping char in front of any text is dropped
# EXCLUDES: a leading quote, backtick or angle bracket kept, a wrapping
#   char of another set trimmed
law redirect_input_clean_trims_lead:
  for +w: Char
  for +s: String
  for wrap: {ri_wrapper(w) == True{} : Bool}
  {Ri.clean(SCon{w, s}) == Ri.clean(s) : String}

# LAW redirect_input_clean_trims_trail (R1): a wrapping char after any text is dropped
# EXCLUDES: a trailing quote, backtick or angle bracket kept, wrappers
#   trimmed on one end only
law redirect_input_clean_trims_trail:
  for +s: String
  for +w: Char
  for wrap: {ri_wrapper(w) == True{} : Bool}
  {Ri.clean(String.append(s, SCon{w, SNil{}})) == Ri.clean(s) : String}

# LAW redirect_input_clean_keeps (R1): a non-empty text with no whitespace or zero-width char that neither starts nor ends with a wrapping char cleans to itself
# EXCLUDES: a wrapping char trimmed inside the text, a char of the text
#   changed or dropped, the text cut
law redirect_input_clean_keeps:
  for +x: Char
  for +t: String
  for quiet: {ri_quiet(SCon{x, t}) == True{} : Bool}
  for head: {ri_wrapper(x) == False{} : Bool}
  for last: {ri_wrap_first(String.reverse(SCon{x, t})) == False{} : Bool}
  {Ri.clean(SCon{x, t}) == SCon{x, t} : String}

# Laws: the paste's code and state (R2, R3)
# -----------------------------------------

# LAW redirect_input_parse_ignores_noise (R1, R2): a whitespace or zero-width char anywhere in a paste changes nothing of its answer
# EXCLUDES: a code or state cut at a line break of a wrapped copy, a
#   space read into a value
law redirect_input_parse_ignores_noise:
  for +a: String
  for +x: Char
  for +b: String
  for noise: {ri_noise(x) == True{} : Bool}
  {Ri.parse(String.append(a, SCon{x, b})) == Ri.parse(String.append(a, b)) : Ri.Answer}

# LAW redirect_input_parse_ignores_wrappers (R1, R2): a paste wrapped in a wrapping char at either end answers as the paste itself
# EXCLUDES: a quote or angle bracket read into the code or the state
law redirect_input_parse_ignores_wrappers:
  for +w1: Char
  for +s: String
  for +w2: Char
  for wrap1: {ri_wrapper(w1) == True{} : Bool}
  for wrap2: {ri_wrapper(w2) == True{} : Bool}
  {Ri.parse(SCon{w1, String.append(s, SCon{w2, SNil{}})}) == Ri.parse(s) : Ri.Answer}

# The paste shapes of Rust's property test (aeabc30d3^:crates/eukhe-core/
# src/auth/redirect_input.rs `render`: an address with the pairs in its
# query or its fragment, a bare query, a `code#state` pair, a bare code),
# each over every value of URL-safe chars (ri_value: one or more chars,
# none whitespace, zero-width, wrapping or one of % + & = # ? /) and every
# text around it that the shape allows.

# LAW redirect_input_query (R2, R3): an address b (any text with no `?`), then `?code=` c `&state=` s and n trailing slashes, answers the code c and the state s, for all values c, s
# EXCLUDES: the code or state read from the address before the query,
#   fields swapped, a value cut or extended, a trailing slash read into
#   the state
law redirect_input_query:
  for +b: String
  for +c: String
  for +s: String
  for +n: Nat
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  for vs: {ri_value(s) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?code=", String.append(c, String.append("&state=", String.append(s, ri_slashes(n))))))) == Ri.Pasted{c, Some{s}} : Ri.Answer}

# LAW redirect_input_query_no_state (R2, R3): an address b with no `?`, then `?code=` c, answers the code c and no state
# EXCLUDES: a state invented (the code, the address or an empty one)
law redirect_input_query_no_state:
  for +b: String
  for +c: String
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?code=", c))) == Ri.Pasted{c, None{}} : Ri.Answer}

# LAW redirect_input_query_no_code (R2, R3): an address b with no `?`, then `?state=` s, answers that it has no code
# EXCLUDES: the state, the address or a default taken as the code
law redirect_input_query_no_code:
  for +b: String
  for +s: String
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vs: {ri_value(s) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?state=", s))) == Ri.Failed{Ri.FMissing{}} : Ri.Answer}

# LAW redirect_input_first_value (R3): in a query `?code=&code=` c `&code=` d (after an address b with no `?`) the code is c: an empty value is skipped and the first non-empty one taken
# EXCLUDES: an empty code taken, the last value taken
law redirect_input_first_value:
  for +b: String
  for +c: String
  for +d: String
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  for vd: {ri_value(d) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?code=&code=", String.append(c, String.append("&code=", d))))) == Ri.Pasted{c, None{}} : Ri.Answer}

# LAW redirect_input_plus_space (R3): a `+` in a value is a space: `?code=` c `+` d (after an address b with no `?`) answers the code c, a space, d
# EXCLUDES: a `+` kept, dropped or read as a separator
law redirect_input_plus_space:
  for +b: String
  for +c: String
  for +d: String
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  for vd: {ri_value(d) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?code=", String.append(c, SCon{'+', d})))) == Ri.Pasted{String.append(c, SCon{' ', d}), None{}} : Ri.Answer}

# LAW redirect_input_error_wins (R3): an address b with no `?`, then `?code=` c `&error=` e `&error_description=` d, answers the provider failure e with the description d, though a code came first
# EXCLUDES: the code taken over an OAuth error, the description lost or
#   read from another field
law redirect_input_error_wins:
  for +b: String
  for +c: String
  for +e: String
  for +d: String
  for nq: {ri_lacks(b, 63) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  for ve: {ri_value(e) == True{} : Bool}
  for vd: {ri_value(d) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("?code=", String.append(c, String.append("&error=", String.append(e, String.append("&error_description=", d))))))) == Ri.Failed{Ri.FProvider{e, Some{d}}} : Ri.Answer}

# LAW redirect_input_fragment (R2, R3): a scheme b (no `:` or `?`), `://`, an address h (no `?` or `#`), then `#code=` c `&state=` s answers the code c and the state s
# EXCLUDES: the fragment of an address with a scheme and no query
#   ignored, the address part read as parameters
law redirect_input_fragment:
  for +b: String
  for +h: String
  for +c: String
  for +s: String
  for nb: {Bool.and(ri_lacks(b, 58), ri_lacks(b, 63)) == True{} : Bool}
  for nh: {Bool.and(ri_lacks(h, 63), ri_lacks(h, 35)) == True{} : Bool}
  for vc: {ri_value(c) == True{} : Bool}
  for vs: {ri_value(s) == True{} : Bool}
  {Ri.parse(String.append(b, String.append("://", String.append(h, String.append("#code=", String.append(c, String.append("&state=", s))))))) == Ri.Pasted{c, Some{s}} : Ri.Answer}

# LAW redirect_input_bare_query (R2, R3): a bare query `code=` c `&state=` s answers the code c and the state s
# EXCLUDES: a bare query read as a bare code
law redirect_input_bare_query:
  for +c: String
  for +s: String
  for vc: {ri_value(c) == True{} : Bool}
  for vs: {ri_value(s) == True{} : Bool}
  {Ri.parse(String.append("code=", String.append(c, String.append("&state=", s)))) == Ri.Pasted{c, Some{s}} : Ri.Answer}

# LAW redirect_input_pair (R2): a pair c `#` s of values answers the code c and the state s
# EXCLUDES: the pair read as one code, the state lost
law redirect_input_pair:
  for +c: String
  for +s: String
  for vc: {ri_value(c) == True{} : Bool}
  for vs: {ri_value(s) == True{} : Bool}
  {Ri.parse(String.append(c, SCon{'#', s})) == Ri.Pasted{c, Some{s}} : Ri.Answer}

# LAW redirect_input_bare_code (R2): a value c alone answers the code c and no state
# EXCLUDES: a bare code refused, a state invented
law redirect_input_bare_code:
  for +c: String
  for vc: {ri_value(c) == True{} : Bool}
  {Ri.parse(c) == Ri.Pasted{c, None{}} : Ri.Answer}

# Laws: the state check (R4)
# --------------------------

# LAW redirect_input_verify_none (R4): a paste without a state takes the login's state e
# EXCLUDES: a missing state refused, the code changed
law redirect_input_verify_none:
  for c: String
  for e: String
  {Ri.verify(c, None{}, e) == Ri.Pasted{c, Some{e}} : Ri.Answer}

# LAW redirect_input_verify_same (R4): a paste with the login's own state e keeps it and its code
# EXCLUDES: the login's state refused
law redirect_input_verify_same:
  for c: String
  for +e: String
  {Ri.verify(c, Some{e}, e) == Ri.Pasted{c, Some{e}} : Ri.Answer}

# LAW redirect_input_verify_only_same (R4): a paste whose state s passes the check against the login's state e has s equal to e, and keeps its code c and state
# EXCLUDES: another login's state accepted, the paste's state replaced
law redirect_input_verify_only_same:
  for +c: String
  for +s: String
  for +e: String
  for +c2: String
  for +m: Maybe<&2, String>
  for ok: {Ri.verify(c, Some{s}, e) == Ri.Pasted{c2, m} : Ri.Answer}
  {(s, (c2, m)) == (e, (c, Some{s})) : String & (String & Maybe<&2, String>)}

# LAW redirect_input_verify_other (R4): a paste whose state s is not the login's state e is a state mismatch
# EXCLUDES: another failure for a mismatch, a default
law redirect_input_verify_other:
  for c: String
  for +s: String
  for +e: String
  for differ: {String.eq(s, e) == False{} : Bool}
  {Ri.verify(c, Some{s}, e) == Ri.Failed{Ri.FMismatch{}} : Ri.Answer}

# Laws: the texts (R5)
# --------------------

# R5's texts are anchored only (redirect_input_text_example: Rust's four
# failure texts and two notices): no source outside eukhe's code states
# them (omp has no such paste loop), and a law whose spec spells the same
# literals the model concatenates would compare the model with itself.

# LAW redirect_input_notice_reason (R5): an error text w1 r d w2 (w1, w2 whitespace, d only `.`s, r empty or not starting with whitespace, not ending with `.`, and not ending with whitespace when d is empty) gives the notice of the reason r
# EXCLUDES: whitespace or trailing dots kept, a leading dot dropped, a dot
#   before trailing whitespace kept, dots inside the reason dropped,
#   whitespace before the dots dropped
law redirect_input_notice_reason:
  for +w1: String
  for +r: String
  for +d: String
  for +w2: String
  for sp1: {ri_spaces(w1) == True{} : Bool}
  for sp2: {ri_spaces(w2) == True{} : Bool}
  for dd: {ri_dots(d) == True{} : Bool}
  for head: {ri_space_first(r) == False{} : Bool}
  for tail: {ri_dot_first(String.reverse(r)) == False{} : Bool}
  for bare: {Bool.and(String.is_empty(d), ri_space_first(String.reverse(r))) == False{} : Bool}
  {Ri.notice(String.append(w1, String.append(r, String.append(d, w2)))) == ri_notice_of(r) : String}

# Examples (Rust's tests, aeabc30d3^:crates/eukhe-core/src/auth/
# redirect_input.rs and the from_utf8_lossy table)
# --------------------------------------------------------------------

# LAW redirect_input_parse_example (R2, R3): anchor: Rust's address shapes
# EXCLUDES: a parse that drifts from the shapes Rust's tests pasted
law redirect_input_parse_example:
  {[Ri.parse("h:1/cb?code=a%2Bb%20c&state=s%26t"), Ri.parse("h:1/cb/?code=a&state=s/#_"), Ri.parse("x://h/cb#code=a&state=s"), Ri.parse(" <h:1/cb?x=1&code=a> "), Ri.parse("state=s&code=a"), Ri.parse("  a#s\n"), Ri.parse("`a==`"), Ri.parse("x://h/cb?code=&state=s"), Ri.parse("#s"), Ri.parse("state=s"), Ri.parse("x://h/cb")] == [Ri.Pasted{"a+b c", Some{"s&t"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", None{}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a==", None{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}] : List<&2, Ri.Answer>}

# LAW redirect_input_error_example (R3): anchor: an OAuth error wins over
# the code and carries its description
# EXCLUDES: a parse that drifts from Rust's error test
law redirect_input_error_example:
  {[Ri.parse("?code=c&error=e&error_description=d+x"), Ri.parse("error=e")] == [Ri.Failed{Ri.FProvider{"e", Some{"d x"}}}, Ri.Failed{Ri.FProvider{"e", None{}}}] : List<&2, Ri.Answer>}

# LAW redirect_input_decode_example (R3): anchor: Rust's from_utf8_lossy on
# escaped bytes: a whole char, a truncated sequence, a surrogate, a value
# past U+10FFFF, an escape that is no escape, an escaped name
# EXCLUDES: more or fewer U+FFFD than from_utf8_lossy's maximal subparts
#   on these bytes
law redirect_input_decode_example:
  {[Ri.parse("code=%E2%82%ac"), Ri.parse("code=%E2%82x%F0"), Ri.parse("code=%ED%A0%80"), Ri.parse("code=%F4%90%80"), Ri.parse("code=%zz%4"), Ri.parse("?co%64e=a+b"), Ri.parse("code=%C3%28%C0")] == [Ri.Pasted{"\u{20AC}", None{}}, Ri.Pasted{"\u{FFFD}x\u{FFFD}", None{}}, Ri.Pasted{"\u{FFFD}\u{FFFD}\u{FFFD}", None{}}, Ri.Pasted{"\u{FFFD}\u{FFFD}\u{FFFD}", None{}}, Ri.Pasted{"%zz%4", None{}}, Ri.Pasted{"a b", None{}}, Ri.Pasted{"\u{FFFD}(\u{FFFD}", None{}}] : List<&2, Ri.Answer>}

# LAW redirect_input_verify_example (R4): anchor: Rust's state checks
# EXCLUDES: a check that drifts from Rust's state test
law redirect_input_verify_example:
  {[Ri.verify("c", Some{"s"}, "s"), Ri.verify("c", Some{"s"}, "t"), Ri.verify("c", None{}, "t")] == [Ri.Pasted{"c", Some{"s"}}, Ri.Failed{Ri.FMismatch{}}, Ri.Pasted{"c", Some{"t"}}] : List<&2, Ri.Answer>}

# LAW redirect_input_text_example (R5): anchor: Rust's texts: the four
# failure shapes and two notices
# EXCLUDES: a text that drifts from Rust's Display and notice tests
law redirect_input_text_example:
  {[Ri.text(Ri.FMissing{}), Ri.text(Ri.FMismatch{}), Ri.text(Ri.FProvider{"e", Some{"d"}}), Ri.text(Ri.FProvider{"e", None{}}), Ri.notice(" x. \n"), Ri.notice("a .")] == ["That address has no authorization code. Paste the full address of the page your browser ended on.", "That address is from a different login attempt (state mismatch). Paste the address from the browser tab this login opened.", "The sign-in page reported an error: e (d). Open the login link again and sign in, then paste the new address.", "The sign-in page reported an error: e. Open the login link again and sign in, then paste the new address.", "Login did not complete: x. Paste the address again, or open the login link again and sign in.", "Login did not complete: a . Paste the address again, or open the login link again and sign in."] : List<&2, String>}

# Laws: the entry (R6)
# --------------------

# LAW redirect_input_entry_answers (R6): the entry answers every request
# Rust spells, every length within the wire, with the model's answer
# (pinned by the R1-R5 laws) spelled
# EXCLUDES: fields read in another order, a tag misread, the state and the
#   login's state swapped, a default
law redirect_input_entry_answers:
  for +q: FRi.Req
  for fit: {ri_fit_req(q) == True{} : Bool}
  {FRi.ffi(ri_w_req(q, "")) == ri_w_reply(q) : String}

# LAW redirect_input_entry_left_over (R6): a spelled request followed by
# more input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law redirect_input_entry_left_over:
  for +q: FRi.Req
  for +c: Char
  for +t: String
  for fit: {ri_fit_req(q) == True{} : Bool}
  {FRi.ffi(ri_w_req(q, SCon{c, t})) == Wr.err("redirect_input: malformed request") : String}

# LAW redirect_input_entry_exact (R6): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, a Maybe
#   tag past 1, a failure tag past 2, a short field, input left over)
law redirect_input_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRi.ffi(s)) == False{} : Bool}
  exs q: FRi.Req
  {s == ri_w_req(q, "") : String} & {ri_fit_req(q) == True{} : Bool}

# LAW redirect_input_entry_refuses (R6): every error the entry answers is
# exactly `E redirect_input: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law redirect_input_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FRi.ffi(s)) == True{} : Bool}
  {FRi.ffi(s) == Wr.err("redirect_input: malformed request") : String}

# LAW redirect_input_entry_example (R6): anchor: the wire strings Rust sends
# and the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law redirect_input_entry_example:
  {[FRi.ffi("1,3,a#b"), FRi.ffi("2,1,c1,1,s1,t"), FRi.ffi("3,2,1,e1,1,d"), FRi.ffi("0,3, x "), FRi.ffi("1,6,code=a"), FRi.ffi("3,3,"), FRi.ffi("2,1,c2,1,s1,t"), FRi.ffi("5,"), FRi.ffi("0,1,ax")] == ["0,1,a1,1,b", "1,1,", "109,The sign-in page reported an error: e (d). Open the login link again and sign in, then paste the new address.", "1,x", "0,1,a0,", Wr.err("redirect_input: malformed request"), Wr.err("redirect_input: malformed request"), Wr.err("redirect_input: malformed request"), Wr.err("redirect_input: malformed request")] : List<&2, String>}
