# eukhe: the laws of area redirect_input

import Base
import ../bend/redirect_input.bend as Ri
import ../bend/ffi_redirect_input.bend as FRi
import ../bend/gateway_answer.bend as Ga
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
#     (Rust `char::is_whitespace`: Ga.space) or one of U+200B, U+200C,
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
#     length within the wire) with the spec's answer (clean, text, notice:
#     the text; parse, verify: 0 pasted: the code and the state as
#     Maybe<String> | 1 failed: the failure), reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E redirect_input: malformed request`.

# Spec helpers
# ------------

# Clean
# -----

def ri_zero_width(c: Char) -> Bool:
  Ga.in(Char.to_u32(c), [8203, 8204, 8205, 8288, 65279])

def ri_wrapper(c: Char) -> Bool:
  Ga.in(Char.to_u32(c), [34, 39, 96, 60, 62, 8220, 8221, 8216, 8217])

def ri_compact.at(drop: Bool, c: Char, r: String) -> String:
  match drop:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# s without whitespace and zero-width chars
def ri_compact(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      ri_compact.at(Bool.or(Ga.space(c), ri_zero_width(c)), c, ri_compact(t))

def ri_unwrap.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading wrapping chars
def ri_unwrap(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ri_unwrap.at(ri_wrapper(c), c, t, ri_unwrap(t))

# the paste as typed: compacted, then wrapping chars trimmed at both ends
def ri_clean(s: String) -> String:
  String.reverse(ri_unwrap(String.reverse(ri_unwrap(ri_compact(s)))))

# Text
# ----

def ri_split.at(b: Bool, c: Char, t: String, r: Maybe<&2, Ri.Cut>) -> Maybe<&2, Ri.Cut>:
  match b:
    case True{}:
      Some{Ri.Cut{SNil{}, t}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Ri.Cut{h, u}:
              Some{Ri.Cut{SCon{c, h}, u}}

# s split at its first `sep` (none without one)
def ri_split(s: String, +sep: Char) -> Maybe<&2, Ri.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      ri_split.at(Char.is_eq(c, sep), c, t, ri_split(t, sep))

def ri_scheme.at(b: Bool, t: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{String.drop(t, 2n)}
    case False{}:
      r

# the text after the first `://` (none without one)
def ri_scheme(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      ri_scheme.at(String.starts_with(SCon{c, t}, "://"), t, ri_scheme(t))

def ri_slashes.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def ri_slashes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ri_slashes.at(Char.is_eq(c, '/'), c, t, ri_slashes(t))

# s without its trailing `/`s
def ri_unslash(s: String) -> String:
  String.reverse(ri_slashes(String.reverse(s)))

# the text after the first `#` (empty without one)
def ri_fragment(m: Maybe<&2, Ri.Cut>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{x}:
      match x:
        case Ri.Cut{h, u}:
          u

# Decoding
# --------

def ri_hexv.at(dec: Bool, low: Bool, up: Bool, +x: U32) -> Maybe<&2, U32>:
  match dec:
    case True{}:
      Some{U32.sub(x, 48)}
    case False{}:
      match low:
        case True{}:
          Some{U32.sub(x, 87)}
        case False{}:
          match up:
            case True{}:
              Some{U32.sub(x, 55)}
            case False{}:
              None{}

def ri_within(+x: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

# the value of an ASCII hex digit
def ri_hexv(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      ri_hexv.at(ri_within(x, 48, 57), ri_within(x, 97, 102), ri_within(x, 65, 70), x)

# What a char in plain text adds: `%` nothing yet, `+` a space
def ri_plain.out(pct: Bool, plus: Bool, c: Char) -> List<&2, Ri.Piece>:
  match pct:
    case True{}:
      []
    case False{}:
      match plus:
        case True{}:
          [Ri.UChar{' '}]
        case False{}:
          [Ri.UChar{c}]

def ri_plain.next(pct: Bool) -> Ri.Pct:
  match pct:
    case True{}:
      Ri.PSign{}
    case False{}:
      Ri.PPlain{}

def ri_sign.out(m: Maybe<&2, U32>, +c: Char) -> List<&2, Ri.Piece>:
  match m:
    case None{}:
      Ri.UChar{'%'} <> ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Some{v}:
      []

def ri_sign.next(m: Maybe<&2, U32>, +c: Char) -> Ri.Pct:
  match m:
    case None{}:
      ri_plain.next(Char.is_eq(c, '%'))
    case Some{v}:
      Ri.PDigit{c, v}

def ri_digit.out(m: Maybe<&2, U32>, h: Char, v: U32, +c: Char) -> List<&2, Ri.Piece>:
  match m:
    case None{}:
      Ri.UChar{'%'} <> Ri.UChar{h} <> ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Some{w}:
      [Ri.UByte{U32.add(U32.mul(v, 16), w)}]

def ri_digit.next(m: Maybe<&2, U32>, +c: Char) -> Ri.Pct:
  match m:
    case None{}:
      ri_plain.next(Char.is_eq(c, '%'))
    case Some{w}:
      Ri.PPlain{}

# what a char adds in a state: a `%` not followed by two hex digits is a
# char, the chars after it read again as plain text
def ri_pout(st: Ri.Pct, +c: Char) -> List<&2, Ri.Piece>:
  match st:
    case Ri.PPlain{}:
      ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Ri.PSign{}:
      ri_sign.out(ri_hexv(c), c)
    case Ri.PDigit{h, v}:
      ri_digit.out(ri_hexv(c), h, v, c)

# the state after a char
def ri_pnext(st: Ri.Pct, +c: Char) -> Ri.Pct:
  match st:
    case Ri.PPlain{}:
      ri_plain.next(Char.is_eq(c, '%'))
    case Ri.PSign{}:
      ri_sign.next(ri_hexv(c), c)
    case Ri.PDigit{h, v}:
      ri_digit.next(ri_hexv(c), c)

def ri_pend(st: Ri.Pct) -> List<&2, Ri.Piece>:
  match st:
    case Ri.PPlain{}:
      []
    case Ri.PSign{}:
      [Ri.UChar{'%'}]
    case Ri.PDigit{h, v}:
      [Ri.UChar{'%'}, Ri.UChar{h}]

# the pieces of a text from a state: `+` a space, `%` and two hex digits a
# byte, any other `%` a char
def ri_units(s: String, +st: Ri.Pct) -> List<&2, Ri.Piece>:
  match s:
    case SNil{}:
      ri_pend(st)
    case SCon{+c, t}:
      List.append(&2, Ri.Piece, ri_pout(st, c), ri_units(t, ri_pnext(st, c)))

def ri_bad() -> Char:
  Chr{65533}

def ri_lead.four.at(f0: Bool, f1: Bool, f4: Bool, b: U32) -> Ri.UStep:
  match f0:
    case True{}:
      Ri.UStep{SNil{}, Ri.UNeed{2n, 0, 144, 191}}
    case False{}:
      match f1:
        case True{}:
          Ri.UStep{SNil{}, Ri.UNeed{2n, U32.sub(b, 240), 128, 191}}
        case False{}:
          match f4:
            case True{}:
              Ri.UStep{SNil{}, Ri.UNeed{2n, 4, 128, 143}}
            case False{}:
              Ri.UStep{SCon{ri_bad(), SNil{}}, Ri.UIdle{}}

# a byte that leads no 1-3 byte char: a 4-byte lead, else invalid
def ri_lead.four(+b: U32) -> Ri.UStep:
  ri_lead.four.at(U32.is_eq(b, 240), ri_within(b, 241, 243), U32.is_eq(b, 244), b)

def ri_lead.three.at(e0: Bool, ed: Bool, e1: Bool, +b: U32) -> Ri.UStep:
  match e0:
    case True{}:
      Ri.UStep{SNil{}, Ri.UNeed{1n, 0, 160, 191}}
    case False{}:
      match ed:
        case True{}:
          Ri.UStep{SNil{}, Ri.UNeed{1n, 13, 128, 159}}
        case False{}:
          match e1:
            case True{}:
              Ri.UStep{SNil{}, Ri.UNeed{1n, U32.sub(b, 224), 128, 191}}
            case False{}:
              ri_lead.four(b)

# a byte that leads no 1-2 byte char: a 3-byte lead, else lead.four
def ri_lead.three(+b: U32) -> Ri.UStep:
  ri_lead.three.at(U32.is_eq(b, 224), U32.is_eq(b, 237), ri_within(b, 225, 239), b)

def ri_lead.at(ascii: Bool, two: Bool, +b: U32) -> Ri.UStep:
  match ascii:
    case True{}:
      Ri.UStep{SCon{Chr{b}, SNil{}}, Ri.UIdle{}}
    case False{}:
      match two:
        case True{}:
          Ri.UStep{SNil{}, Ri.UNeed{0n, U32.sub(b, 192), 128, 191}}
        case False{}:
          ri_lead.three(b)

# a byte between chars
def ri_lead(+b: U32) -> Ri.UStep:
  ri_lead.at(U32.is_lt(b, 128), ri_within(b, 194, 223), b)

def ri_cont.at(more: Nat, +v: U32) -> Ri.UStep:
  match more:
    case 0n:
      Ri.UStep{SCon{Chr{v}, SNil{}}, Ri.UIdle{}}
    case 1n+m:
      Ri.UStep{SNil{}, Ri.UNeed{m, v, 128, 191}}

def ri_broken(s: Ri.UStep) -> Ri.UStep:
  match s:
    case Ri.UStep{o, n}:
      Ri.UStep{SCon{ri_bad(), o}, n}

def ri_cont(ok: Bool, more: Nat, acc: U32, +b: U32) -> Ri.UStep:
  match ok:
    case True{}:
      ri_cont.at(more, U32.add(U32.mul(acc, 64), U32.sub(b, 128)))
    case False{}:
      ri_broken(ri_lead(b))

def ri_ustep(st: Ri.Utf, u: Ri.Piece) -> Ri.UStep:
  match st:
    case Ri.UIdle{}:
      match u:
        case Ri.UChar{c}:
          Ri.UStep{SCon{c, SNil{}}, Ri.UIdle{}}
        case Ri.UByte{+b}:
          ri_lead(b)
    case Ri.UNeed{more, acc, +lo, +hi}:
      match u:
        case Ri.UChar{c}:
          Ri.UStep{SCon{ri_bad(), SCon{c, SNil{}}}, Ri.UIdle{}}
        case Ri.UByte{+b}:
          ri_cont(ri_within(b, lo, hi), more, acc, b)

def ri_uend(st: Ri.Utf) -> String:
  match st:
    case Ri.UIdle{}:
      SNil{}
    case Ri.UNeed{more, acc, lo, hi}:
      SCon{ri_bad(), SNil{}}

def ri_uout(s: Ri.UStep) -> String:
  match s:
    case Ri.UStep{o, n}:
      o

def ri_unext(s: Ri.UStep) -> Ri.Utf:
  match s:
    case Ri.UStep{o, n}:
      n

# the text of pieces, bytes read as UTF-8: each maximal invalid part U+FFFD
def ri_utf(us: List<&2, Ri.Piece>, +st: Ri.Utf) -> String:
  match us:
    case Nil{}:
      ri_uend(st)
    case +u <> rest:
      String.append(ri_uout(ri_ustep(st, u)), ri_utf(rest, ri_unext(ri_ustep(st, u))))

# a decoded name or value
def ri_decode(s: String) -> String:
  ri_utf(ri_units(s, Ri.PPlain{}), Ri.UIdle{})

# Parameters
# ----------

def ri_param(m: Maybe<&2, Ri.Cut>, +s: String) -> Ri.Param:
  match m:
    case None{}:
      Ri.Param{ri_decode(s), SNil{}}
    case Some{x}:
      match x:
        case Ri.Cut{h, u}:
          Ri.Param{ri_decode(h), ri_decode(u)}

def ri_params.at(empty: Bool, +p: String, r: List<&2, Ri.Param>) -> List<&2, Ri.Param>:
  match empty:
    case True{}:
      r
    case False{}:
      ri_param(ri_split(p, '='), p) <> r

def ri_params.go(ps: List<&2, String>) -> List<&2, Ri.Param>:
  match ps:
    case Nil{}:
      []
    case +p <> rest:
      ri_params.at(String.is_empty(p), p, ri_params.go(rest))

# the parameters of a carrier, in order (empty pairs skipped)
def ri_params(s: String) -> List<&2, Ri.Param>:
  ri_params.go(String.split(s, '&'))

def ri_find.at(b: Bool, v: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      r

# the first non-empty value of a name
def ri_find(+name: String, ps: List<&2, Ri.Param>) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case p <> rest:
      match p:
        case Ri.Param{n, +v}:
          ri_find.at(Bool.and(String.eq(n, name), Bool.not(String.is_empty(v))), v, ri_find(name, rest))

def ri_get.at(m: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      r
    case Some{v}:
      Some{v}

# a name's value: the first carrier that has one
def ri_get(+name: String, cs: List<&2, String>) -> Maybe<&2, String>:
  match cs:
    case Nil{}:
      None{}
    case c <> rest:
      ri_get.at(ri_find(name, ri_params(c)), ri_get(name, rest))

def ri_from_code(m: Maybe<&2, String>, +cs: List<&2, String>) -> Ri.Answer:
  match m:
    case None{}:
      Ri.Failed{Ri.FMissing{}}
    case Some{c}:
      Ri.Pasted{c, ri_get("state", cs)}

def ri_from_error(m: Maybe<&2, String>, +cs: List<&2, String>) -> Ri.Answer:
  match m:
    case Some{e}:
      Ri.Failed{Ri.FProvider{e, ri_get("error_description", cs)}}
    case None{}:
      ri_from_code(ri_get("code", cs), cs)

# the answer of carriers: an error wins, then the code and its state
def ri_from_params(+cs: List<&2, String>) -> Ri.Answer:
  ri_from_error(ri_get("error", cs), cs)

# Parse
# -----

def ri_key(m: Maybe<&2, Ri.Cut>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Ri.Cut{+h, u}:
          Bool.or(String.eq(h, "code"), Bool.or(String.eq(h, "state"), String.eq(h, "error")))

def ri_carries.go(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(ri_key(ri_split(p, '=')), ri_carries.go(rest))

# a text holds a `code=`, `state=` or `error=` pair
def ri_carries(s: String) -> Bool:
  ri_carries.go(String.split(s, '&'))

def ri_bare.state(empty: Bool, f: String) -> Maybe<&2, String>:
  match empty:
    case True{}:
      None{}
    case False{}:
      Some{f}

def ri_bare.at(in_head: Bool, in_frag: Bool, empty: Bool, h: String, +f: String) -> Ri.Answer:
  match in_head:
    case True{}:
      ri_from_params([ri_unslash(h)])
    case False{}:
      match in_frag:
        case True{}:
          ri_from_params([f])
        case False{}:
          match empty:
            case True{}:
              Ri.Failed{Ri.FMissing{}}
            case False{}:
              Ri.Pasted{h, ri_bare.state(String.is_empty(f), f)}

# a text without `?` or `://`: its head before the first `#`, and the
# fragment after it
def ri_bare(+h: String, +f: String) -> Ri.Answer:
  ri_bare.at(ri_carries(h), ri_carries(f), String.is_empty(h), h, f)

def ri_parse.hash(m: Maybe<&2, Ri.Cut>, v: String) -> Ri.Answer:
  match m:
    case None{}:
      ri_bare(v, SNil{})
    case Some{x}:
      match x:
        case Ri.Cut{h, f}:
          ri_bare(h, f)

def ri_parse.scheme(m: Maybe<&2, String>, +v: String) -> Ri.Answer:
  match m:
    case Some{rest}:
      ri_from_params([ri_fragment(ri_split(rest, '#'))])
    case None{}:
      ri_parse.hash(ri_split(v, '#'), v)

def ri_parse.query(m: Maybe<&2, Ri.Cut>, rest: String) -> Ri.Answer:
  match m:
    case None{}:
      ri_from_params([ri_unslash(rest), SNil{}])
    case Some{x}:
      match x:
        case Ri.Cut{q, f}:
          ri_from_params([ri_unslash(q), f])

def ri_parse.at(m: Maybe<&2, Ri.Cut>, +v: String) -> Ri.Answer:
  match m:
    case Some{x}:
      match x:
        case Ri.Cut{h, +rest}:
          ri_parse.query(ri_split(rest, '#'), rest)
    case None{}:
      ri_parse.scheme(ri_scheme(v), v)

# a paste's code and state, or why it has none
def ri_parse(s: String) -> Ri.Answer:
  +v = ri_clean(s)
  ri_parse.at(ri_split(v, '?'), v)

# State check and texts
# ---------------------

def ri_verify.at(same: Bool, code: String, s: String) -> Ri.Answer:
  match same:
    case True{}:
      Ri.Pasted{code, Some{s}}
    case False{}:
      Ri.Failed{Ri.FMismatch{}}

# a paste's state against the login's own: equal, or none (the login's)
def ri_verify(code: String, m: Maybe<&2, String>, +expected: String) -> Ri.Answer:
  match m:
    case None{}:
      Ri.Pasted{code, Some{expected}}
    case Some{+s}:
      ri_verify.at(String.eq(s, expected), code, s)

def ri_described(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{d}:
      String.concat([" (", d, ")"])

# the user-facing text of a failure
def ri_text(f: Ri.Fail) -> String:
  match f:
    case Ri.FMissing{}:
      "That address has no authorization code. Paste the full address of the page your browser ended on."
    case Ri.FMismatch{}:
      "That address is from a different login attempt (state mismatch). Paste the address from the browser tab this login opened."
    case Ri.FProvider{e, d}:
      String.concat(["The sign-in page reported an error: ", e, ri_described(d), ". Open the login link again and sign in, then paste the new address."])

def ri_trim_start.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def ri_trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ri_trim_start.at(Ga.space(c), c, t, ri_trim_start(t))

def ri_dots.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def ri_dots(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ri_dots.at(Char.is_eq(c, '.'), c, t, ri_dots(t))

# the reason of a failed exchange: trimmed, then its trailing `.`s dropped
def ri_reason(s: String) -> String:
  String.reverse(ri_dots(ri_trim_start(String.reverse(ri_trim_start(s)))))

# the notice of a failed token exchange
def ri_notice(s: String) -> String:
  String.concat(["Login did not complete: ", ri_reason(s), ". Paste the address again, or open the login link again and sign in."])

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

def ri_w_reply(q: FRi.Req) -> String:
  match q:
    case FRi.QClean{x}:
      Wr.put_str(ri_clean(x), "")
    case FRi.QParse{x}:
      ri_w_answer(ri_parse(x))
    case FRi.QVerify{c, m, e}:
      ri_w_answer(ri_verify(c, m, e))
    case FRi.QText{f}:
      Wr.put_str(ri_text(f), "")
    case FRi.QNotice{x}:
      Wr.put_str(ri_notice(x), "")

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

# Laws: the model
# ---------------

# LAW redirect_input_clean_spec (R1): every paste cleans to the spec's
# EXCLUDES: whitespace or a zero-width char kept, a wrapper trimmed inside
#   the text or on one end only, another whitespace set
law redirect_input_clean_spec:
  for +s: String
  {Ri.clean(s) == ri_clean(s) : String}

# LAW redirect_input_parse_spec (R1-R3): every paste answers the spec's code
# and state, or failure
# EXCLUDES: the fragment read before the query, a carrier without its
#   trailing `/`s dropped where Rust drops them, a value not decoded or
#   decoded twice, a `+` kept, an invalid escape dropped, an invalid UTF-8
#   part replaced by more or fewer U+FFFD, an empty value taken, a later
#   carrier before an earlier one, the code before an error
law redirect_input_parse_spec:
  for +s: String
  {Ri.parse(s) == ri_parse(s) : Ri.Answer}

# LAW redirect_input_verify_spec (R4): every state check is the spec's
# EXCLUDES: a missing state refused, another state accepted, the paste's
#   state replaced by the login's
law redirect_input_verify_spec:
  for +c: String
  for +m: Maybe<&2, String>
  for +e: String
  {Ri.verify(c, m, e) == ri_verify(c, m, e) : Ri.Answer}

# LAW redirect_input_text_spec (R5): every failure's text is the spec's
# EXCLUDES: a changed text, the description shown without its parentheses
#   or when absent
law redirect_input_text_spec:
  for +f: Ri.Fail
  {Ri.text(f) == ri_text(f) : String}

# LAW redirect_input_notice_spec (R5): every exchange error's notice is the
# spec's
# EXCLUDES: whitespace or trailing dots kept, a leading dot dropped, a dot
#   before trailing whitespace kept
law redirect_input_notice_spec:
  for +s: String
  {Ri.notice(s) == ri_notice(s) : String}

# LAW redirect_input_parse_example (R2, R3): anchor: Rust's address shapes
# EXCLUDES: a spec that drifts from the Rust it replaced
law redirect_input_parse_example:
  {[Ri.parse("h:1/cb?code=a%2Bb%20c&state=s%26t"), Ri.parse("h:1/cb/?code=a&state=s/#_"), Ri.parse("x://h/cb#code=a&state=s"), Ri.parse(" <h:1/cb?x=1&code=a> "), Ri.parse("state=s&code=a"), Ri.parse("  a#s\n"), Ri.parse("`a==`"), Ri.parse("x://h/cb?code=&state=s"), Ri.parse("#s"), Ri.parse("state=s"), Ri.parse("x://h/cb")] == [Ri.Pasted{"a+b c", Some{"s&t"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", None{}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a", Some{"s"}}, Ri.Pasted{"a==", None{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}, Ri.Failed{Ri.FMissing{}}] : List<&2, Ri.Answer>}

# LAW redirect_input_error_example (R3): anchor: an OAuth error wins over
# the code and carries its description
# EXCLUDES: a spec that drifts from the Rust it replaced
law redirect_input_error_example:
  {[Ri.parse("?code=c&error=e&error_description=d+x"), Ri.parse("error=e")] == [Ri.Failed{Ri.FProvider{"e", Some{"d x"}}}, Ri.Failed{Ri.FProvider{"e", None{}}}] : List<&2, Ri.Answer>}

# LAW redirect_input_decode_example (R3): anchor: Rust's from_utf8_lossy on
# escaped bytes: a whole char, a truncated sequence, a surrogate, a value
# past U+10FFFF, an escape that is no escape, an escaped name
# EXCLUDES: a spec that drifts from the Rust it replaced
law redirect_input_decode_example:
  {[Ri.parse("code=%E2%82%ac"), Ri.parse("code=%E2%82x%F0"), Ri.parse("code=%ED%A0%80"), Ri.parse("code=%F4%90%80"), Ri.parse("code=%zz%4"), Ri.parse("?co%64e=a+b"), Ri.parse("code=%C3%28%C0")] == [Ri.Pasted{"\u{20AC}", None{}}, Ri.Pasted{"\u{FFFD}x\u{FFFD}", None{}}, Ri.Pasted{"\u{FFFD}\u{FFFD}\u{FFFD}", None{}}, Ri.Pasted{"\u{FFFD}\u{FFFD}\u{FFFD}", None{}}, Ri.Pasted{"%zz%4", None{}}, Ri.Pasted{"a b", None{}}, Ri.Pasted{"\u{FFFD}(\u{FFFD}", None{}}] : List<&2, Ri.Answer>}

# LAW redirect_input_verify_example (R4): anchor: Rust's state checks
# EXCLUDES: a spec that drifts from the Rust it replaced
law redirect_input_verify_example:
  {[Ri.verify("c", Some{"s"}, "s"), Ri.verify("c", Some{"s"}, "t"), Ri.verify("c", None{}, "t")] == [Ri.Pasted{"c", Some{"s"}}, Ri.Failed{Ri.FMismatch{}}, Ri.Pasted{"c", Some{"t"}}] : List<&2, Ri.Answer>}

# LAW redirect_input_text_example (R5): anchor: Rust's texts
# EXCLUDES: a spec that drifts from the Rust it replaced
law redirect_input_text_example:
  {[Ri.text(Ri.FProvider{"e", Some{"d"}}), Ri.notice(" x. \n"), Ri.notice("a .")] == ["The sign-in page reported an error: e (d). Open the login link again and sign in, then paste the new address.", "Login did not complete: x. Paste the address again, or open the login link again and sign in.", "Login did not complete: a . Paste the address again, or open the login link again and sign in."] : List<&2, String>}

# Laws: the entry (R6)
# --------------------

# LAW redirect_input_entry_answers (R6): the entry answers every request
# Rust spells, every length within the wire, with the spec's answer spelled
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
