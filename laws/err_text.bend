# eukhe: the laws of area err_text

import Base
import ../bend/phrase.bend as P
import ../bend/err_text.bend as E
import ../bend/ffi_err_text.bend as FE
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./text_pat.bend as TextPat
import ./phrase.bend as Phrase

# (ET1) Whether provider error texts read as one kind of error
# ------------------------------------------------------------
# bend/err_text.bend, run as the compiled core by bend/ffi_err_text.bend
# (eukhe-bend rules/err_text.rs; asked by eukhe-ai utils/retry.rs,
# api/openai_codex_responses/errors.rs and api/anthropic_messages/client.rs
# in place of their `regex` patterns). Every rule and every list of texts
# is free. The phrase search is pinned by laws/phrase.bend
# (phrase_search_*, phrase_prefix_*: a phrase is found exactly where a part
# of the text matches its items with its edges holding; phrase_any: a list
# is searched phrase by phrase, Phrase.sp_any); the fold by
# laws/text_pat.bend (text_pat_fold). Each rule's table is read from the
# Rust regex literal the core replaced, quoted whole (sp_regex, rx_read).
#
# R1: a text is searched in its folded form: A-Z as a-z, the Kelvin sign
#     U+212A as k, the long s U+017F as s, every other char as itself
#     (what Rust's `(?i)` matches for a lowercase ASCII pattern char). All
#     phrases are lowercase. "gap" is one char that is no line feed, or
#     none (regex `.?`); "jsgap" one char that is no line feed, carriage
#     return, U+2028 or U+2029, or none (the JS `.?`); "digits" one or more
#     ASCII digits (Rust's `\d` takes every Unicode digit: an intended
#     difference). "starting a word": the char before is no word char or
#     the text starts there (regex `\b` before a word char); "a whole
#     word": that, and the char after is no word char or the text ends
#     there (word chars: laws/phrase.bend R2).
# R2: a text is
#     - a limit when its folded form contains one of: "gousagelimiterror",
#       "freeusagelimiterror", "monthly usage limit reached", "available
#       balance", "insufficient_quota", "out of budget", "quota exceeded",
#       "billing", "subscription_sharing_usage_limit_exceeded", "provider
#       admission queue is full", "server requested " digits "s retry
#       delay";
#     - transient when its folded form contains, starting a word,
#       "overloaded", "rate" gap "limit" or "upstream" gap "connect"; as a
#       whole word, "service" gap "unavailable", "server" gap "error",
#       "internal" gap "error", "provider" gap "returned" gap "error",
#       "network" gap "error", "connection" gap "error", "connection" gap
#       "refused", "connection" gap "lost", "websocket" gap "closed",
#       "websocket" gap "error", "server_busy", "too many requests", "408",
#       "429", "500", "502", "503", "504", "520", "524", "529", "fetch
#       failed", "getaddrinfo", "enotfound", "eai_again", "socket hang up",
#       "timed out", "timedout", "time out", "timeout", "terminated",
#       "ended without", "resourceexhausted",
#       "subscription_sharing_usage_unavailable" or
#       "subscription_sharing_user_unavailable"; anywhere, "servers are
#       currently busy", "currently experiencing high demand", "model is at
#       capacity", "exceeded request buffer limit while retrying upstream",
#       "other side closed", "reset before headers", "socket connection was
#       closed", "stream ended before message_stop", "stream ended before a
#       terminal response event", "http2 request did not get a response",
#       "pending stream has been canceled", "you can retry your request",
#       "try your request again" or "please retry your request";
#     - a Codex terminal limit when its folded form contains one of the
#       first eight phrases of a limit;
#     - Codex retryable when its folded form contains one of: "rate" jsgap
#       "limit", "overloaded", "service" jsgap "unavailable", "upstream"
#       jsgap "connect", "connection" jsgap "refused";
#     - a Codex usage code when its folded form contains one of:
#       "usage_limit_reached", "usage_not_included", "rate_limit_exceeded";
#     - a timeout when its folded form contains one of: "timed out",
#       "timedout", "time out", "timeout".
#     A rule holds for a list of texts when it holds for one of them (an
#     empty list: no).
# R3: the entry answers each request Rust writes (rule 0 limit, 1
#     transient, 2 Codex terminal, 3 Codex retryable, 4 Codex usage code, 5
#     timeout; then the texts, every count and length within the wire) with
#     the answer of R2, reads exactly the request and nothing after it, and
#     answers any other input (a rule past 5 too) with the exact error form
#     `E err_text: malformed request`.

# Spec helpers
# ------------

# R1, R2: reading a Rust regex literal into phrases
# -------------------------------------------------
# The rules' tables are read from the Rust regex literals the compiled core
# replaced (git show fd7645581^: crates/eukhe-ai/src/utils/retry.rs
# NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN and
# RETRYABLE_PROVIDER_ERROR_PATTERN, built as `(?i)` then the patterns
# joined by `|`; api/openai_codex_responses/errors.rs TERMINAL_RATE_LIMIT,
# RETRYABLE_TEXT (JS_DOT = `[^\n\r\u{2028}\u{2029}]`), USAGE_LIMIT_CODE;
# api/anthropic_messages/client.rs TIMEOUT), quoted whole below. The
# reader takes the syntax those literals use, as Rust's `regex` reads it:
# `(?i)` (every pattern char is matched in the folded text, so an ASCII
# capital is read as its small letter); `|` between alternatives; a
# literal char; `\b` opening an alternative (starting a word) or closing
# it (a whole word); `.` (one char that is no line feed); `[^...]` (one
# char none of the listed, `\n`, `\r`, `\u{...}` escapes); `\d` (one
# ASCII digit, R1); `?` after a literal (the alternative with and without
# it), after a class (that char or none); `+` after a class (one or more);
# `(?:a|b)` (one of the literal runs). Each alternative becomes one phrase
# per way its optional literals and groups are taken.

# one unit of an alternative, as read
type RxU is Data:
  RxLit{c: U32}
  RxCls{k: P.Cls}
  RxAlt{alts: List<&2, List<&2, P.It>>}
  RxMaybe{c: U32}
  RxOptCls{k: P.Cls}
  RxMany{k: P.Cls}

# where the reader stands in the literal
type RxMode is Data:
  RxPlain{}
  RxEsc{}
  RxOpen{}
  RxOpenQ{}
  RxFlag{}
  RxGroup{alts: List<&2, List<&2, P.It>>, cur: List<&2, P.It>}
  RxClass{cs: List<&2, Char>}
  RxClassEsc{cs: List<&2, Char>}
  RxClassU{cs: List<&2, Char>, v: U32}

# the reader: its mode, the current alternative's edges and units (last
# first), the phrases of the alternatives read
type Rx is Data:
  Rx{m: RxMode, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>}

# the chars the syntax gives a meaning
type RxK is Data:
  RkBack{}
  RkDot{}
  RkLBr{}
  RkRBr{}
  RkQ{}
  RkPlus{}
  RkLPar{}
  RkRPar{}
  RkBar{}
  RkCaret{}
  RkLBrace{}
  RkRBrace{}
  RkOther{}

def rx_is(b: Bool, k: RxK, other: RxK) -> RxK:
  match b:
    case True{}:
      k
    case False{}:
      other

def rx_kind(+x: U32) -> RxK:
  rx_is(U32.is_eq(x, 92), RkBack{}, rx_is(U32.is_eq(x, 46), RkDot{}, rx_is(U32.is_eq(x, 91), RkLBr{}, rx_is(U32.is_eq(x, 93), RkRBr{}, rx_is(U32.is_eq(x, 63), RkQ{}, rx_is(U32.is_eq(x, 43), RkPlus{}, rx_is(U32.is_eq(x, 40), RkLPar{}, rx_is(U32.is_eq(x, 41), RkRPar{}, rx_is(U32.is_eq(x, 124), RkBar{}, rx_is(U32.is_eq(x, 94), RkCaret{}, rx_is(U32.is_eq(x, 123), RkLBrace{}, rx_is(U32.is_eq(x, 125), RkRBrace{}, RkOther{}))))))))))))

def rx_lower.at(up: Bool, +x: U32) -> U32:
  match up:
    case True{}:
      U32.add(x, 32)
    case False{}:
      x

# (?i): a pattern char as the folded text has it (A-Z as a-z)
def rx_lower(c: Char) -> U32:
  +x = Char.to_u32(c)
  rx_lower.at(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), x)

def rx_hex.at(digit: Bool, +x: U32) -> U32:
  match digit:
    case True{}:
      U32.sub(x, 48)
    case False{}:
      U32.sub(rx_lower.at(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), x), 87)

# the value of a hex digit
def rx_hex(c: Char) -> U32:
  +x = Char.to_u32(c)
  rx_hex.at(U32.is_le(x, 57), x)

# `?` after the last unit
def rx_q(us: List<&2, RxU>) -> List<&2, RxU>:
  match us:
    case Nil{}:
      Nil{}
    case u <> t:
      match u:
        case RxLit{c}:
          RxMaybe{c} <> t
        case RxCls{k}:
          RxOptCls{k} <> t
        case RxAlt{a}:
          RxAlt{a} <> t
        case RxMaybe{c}:
          RxMaybe{c} <> t
        case RxOptCls{k}:
          RxOptCls{k} <> t
        case RxMany{k}:
          RxMany{k} <> t

# `+` after the last unit
def rx_plus(us: List<&2, RxU>) -> List<&2, RxU>:
  match us:
    case Nil{}:
      Nil{}
    case u <> t:
      match u:
        case RxCls{k}:
          RxMany{k} <> t
        case RxLit{c}:
          RxLit{c} <> t
        case RxAlt{a}:
          RxAlt{a} <> t
        case RxMaybe{c}:
          RxMaybe{c} <> t
        case RxOptCls{k}:
          RxOptCls{k} <> t
        case RxMany{k}:
          RxMany{k} <> t

# `\b`: opening the alternative, or closing it
def rx_b(us: List<&2, RxU>, st: P.Edge, en: P.Edge, done: List<&2, P.Ph>) -> Rx:
  match us:
    case Nil{}:
      Rx{RxPlain{}, P.EWord{}, en, Nil{}, done}
    case u <> t:
      Rx{RxPlain{}, st, P.EWord{}, u <> t, done}

# the ways a unit is taken, each as items
def rx_ways(u: RxU) -> List<&2, List<&2, P.It>>:
  match u:
    case RxLit{+c}:
      [[P.One{P.CIn{c, c}}]]
    case RxCls{k}:
      [[P.One{k}]]
    case RxAlt{a}:
      a
    case RxMaybe{+c}:
      [[P.One{P.CIn{c, c}}], []]
    case RxOptCls{k}:
      [[P.Opt{k}]]
    case RxMany{+k}:
      [[P.One{k}, P.Star{k}]]

# each way w, then each of rest
def rx_prefix(+w: List<&2, P.It>, rest: List<&2, List<&2, P.It>>) -> List<&2, List<&2, P.It>>:
  match rest:
    case Nil{}:
      Nil{}
    case x <> t:
      List.append(&2, P.It, w, x) <> rx_prefix(w, t)

def rx_cross(ws: List<&2, List<&2, P.It>>, +rest: List<&2, List<&2, P.It>>) -> List<&2, List<&2, P.It>>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> t:
      List.append(&2, List<&2, P.It>, rx_prefix(w, rest), rx_cross(t, rest))

# every way the units (in order) are taken
def rx_expand(us: List<&2, RxU>) -> List<&2, List<&2, P.It>>:
  match us:
    case Nil{}:
      [[]]
    case u <> t:
      rx_cross(rx_ways(u), rx_expand(t))

def rx_phs(+st: P.Edge, +en: P.Edge, xs: List<&2, List<&2, P.It>>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{st, x, en} <> rx_phs(st, en, t)

# the phrases of an alternative read
def rx_alt(st: P.Edge, en: P.Edge, us: List<&2, RxU>) -> List<&2, P.Ph>:
  rx_phs(st, en, rx_expand(List.reverse(&2, RxU, us)))

def rx_plain(k: RxK, c: Char, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match k:
    case RkBack{}:
      Rx{RxEsc{}, st, en, us, done}
    case RkDot{}:
      Rx{RxPlain{}, st, en, RxCls{P.COut{['\n']}} <> us, done}
    case RkLBr{}:
      Rx{RxClass{Nil{}}, st, en, us, done}
    case RkQ{}:
      Rx{RxPlain{}, st, en, rx_q(us), done}
    case RkPlus{}:
      Rx{RxPlain{}, st, en, rx_plus(us), done}
    case RkLPar{}:
      Rx{RxOpen{}, st, en, us, done}
    case RkBar{}:
      Rx{RxPlain{}, P.EFree{}, P.EFree{}, Nil{}, List.append(&2, P.Ph, done, rx_alt(st, en, us))}
    case RkRBr{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}
    case RkRPar{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}
    case RkCaret{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}
    case RkLBrace{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}
    case RkRBrace{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}
    case RkOther{}:
      Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}

def rx_esc(b: Bool, d: Bool, c: Char, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match b:
    case True{}:
      rx_b(us, st, en, done)
    case False{}:
      match d:
        case True{}:
          Rx{RxPlain{}, st, en, RxCls{P.CIn{48, 57}} <> us, done}
        case False{}:
          Rx{RxPlain{}, st, en, RxLit{rx_lower(c)} <> us, done}

def rx_group(k: RxK, +c: Char, alts: List<&2, List<&2, P.It>>, cur: List<&2, P.It>, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match k:
    case RkBar{}:
      Rx{RxGroup{List.append(&2, List<&2, P.It>, alts, [List.reverse(&2, P.It, cur)]), Nil{}}, st, en, us, done}
    case RkRPar{}:
      Rx{RxPlain{}, st, en, RxAlt{List.append(&2, List<&2, P.It>, alts, [List.reverse(&2, P.It, cur)])} <> us, done}
    case RkBack{}:
      Rx{RxGroup{alts, cur}, st, en, us, done}
    case RkDot{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkLBr{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkRBr{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkQ{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkPlus{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkLPar{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkCaret{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkLBrace{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkRBrace{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}
    case RkOther{}:
      Rx{RxGroup{alts, P.One{P.CIn{rx_lower(c), rx_lower(c)}} <> cur}, st, en, us, done}

def rx_class(k: RxK, c: Char, cs: List<&2, Char>, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match k:
    case RkRBr{}:
      Rx{RxPlain{}, st, en, RxCls{P.COut{List.reverse(&2, Char, cs)}} <> us, done}
    case RkBack{}:
      Rx{RxClassEsc{cs}, st, en, us, done}
    case RkCaret{}:
      Rx{RxClass{cs}, st, en, us, done}
    case RkDot{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkLBr{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkQ{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkPlus{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkLPar{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkRPar{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkBar{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkLBrace{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkRBrace{}:
      Rx{RxClass{c <> cs}, st, en, us, done}
    case RkOther{}:
      Rx{RxClass{c <> cs}, st, en, us, done}

def rx_class_esc(n: Bool, r: Bool, u: Bool, c: Char, cs: List<&2, Char>) -> RxMode:
  match n:
    case True{}:
      RxClass{'\n' <> cs}
    case False{}:
      match r:
        case True{}:
          RxClass{'\r' <> cs}
        case False{}:
          match u:
            case True{}:
              RxClassU{cs, 0}
            case False{}:
              RxClass{c <> cs}

def rx_class_u(k: RxK, c: Char, cs: List<&2, Char>, v: U32) -> RxMode:
  match k:
    case RkRBrace{}:
      RxClass{Chr{v} <> cs}
    case RkLBrace{}:
      RxClassU{cs, v}
    case RkBack{}:
      RxClassU{cs, v}
    case RkDot{}:
      RxClassU{cs, v}
    case RkLBr{}:
      RxClassU{cs, v}
    case RkRBr{}:
      RxClassU{cs, v}
    case RkQ{}:
      RxClassU{cs, v}
    case RkPlus{}:
      RxClassU{cs, v}
    case RkLPar{}:
      RxClassU{cs, v}
    case RkRPar{}:
      RxClassU{cs, v}
    case RkBar{}:
      RxClassU{cs, v}
    case RkCaret{}:
      RxClassU{cs, v}
    case RkOther{}:
      RxClassU{cs, U32.add(U32.mul(v, 16), rx_hex(c))}

def rx_open_q(i: Bool, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match i:
    case True{}:
      Rx{RxFlag{}, st, en, us, done}
    case False{}:
      Rx{RxGroup{Nil{}, Nil{}}, st, en, us, done}

def rx_mode(m: RxMode, k: RxK, +c: Char, st: P.Edge, en: P.Edge, us: List<&2, RxU>, done: List<&2, P.Ph>) -> Rx:
  match m:
    case RxPlain{}:
      rx_plain(k, c, st, en, us, done)
    case RxEsc{}:
      +x = Char.to_u32(c)
      rx_esc(U32.is_eq(x, 98), U32.is_eq(x, 100), c, st, en, us, done)
    case RxOpen{}:
      Rx{RxOpenQ{}, st, en, us, done}
    case RxOpenQ{}:
      rx_open_q(U32.is_eq(Char.to_u32(c), 105), st, en, us, done)
    case RxFlag{}:
      Rx{RxPlain{}, st, en, us, done}
    case RxGroup{alts, cur}:
      rx_group(k, c, alts, cur, st, en, us, done)
    case RxClass{cs}:
      rx_class(k, c, cs, st, en, us, done)
    case RxClassEsc{cs}:
      +x = Char.to_u32(c)
      Rx{rx_class_esc(U32.is_eq(x, 110), U32.is_eq(x, 114), U32.is_eq(x, 117), c, cs), st, en, us, done}
    case RxClassU{cs, v}:
      Rx{rx_class_u(k, c, cs, v), st, en, us, done}

def rx_step(q: Rx, +c: Char) -> Rx:
  match q:
    case Rx{m, st, en, us, done}:
      rx_mode(m, rx_kind(Char.to_u32(c)), c, st, en, us, done)

def rx_run(s: String, q: Rx) -> Rx:
  match s:
    case SNil{}:
      q
    case SCon{+c, t}:
      rx_run(t, rx_step(q, c))

def rx_end(q: Rx) -> List<&2, P.Ph>:
  match q:
    case Rx{m, st, en, us, done}:
      List.append(&2, P.Ph, done, rx_alt(st, en, us))

# the phrases of a regex literal: one per way each alternative is taken
def rx_read(s: String) -> List<&2, P.Ph>:
  rx_end(rx_run(s, Rx{RxPlain{}, P.EFree{}, P.EFree{}, Nil{}, Nil{}}))

# retry.rs build_provider_error_pattern: `(?i)` then the patterns joined
# by `|`
def rx_join(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      match t:
        case Nil{}:
          x
        case y <> u:
          String.append(x, String.append("|", rx_join(y <> u)))

def rx_build(+xs: List<&2, String>) -> String:
  String.append("(?i)", rx_join(xs))

# R2: the Rust literals, quoted whole (retry.rs at fd7645581^: each
# pattern of the list as its raw string, `r"\b"` written "\\b" here)

# retry.rs NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN
def sp_rx_limit() -> String:
  rx_build(["GoUsageLimitError", "FreeUsageLimitError", "Monthly usage limit reached", "available balance", "insufficient_quota", "out of budget", "quota exceeded", "billing", "subscription_sharing_usage_limit_exceeded", "provider admission queue is full", "server requested \\d+s retry delay"])

# retry.rs RETRYABLE_PROVIDER_ERROR_PATTERN
def sp_rx_transient() -> String:
  rx_build(["\\boverloaded", "\\bserver_busy\\b", "servers are currently busy", "currently experiencing high demand", "model is at capacity", "\\brate.?limit", "\\btoo many requests\\b", "\\b(?:408|429|500|502|503|504|520|524|529)\\b", "\\bservice.?unavailable\\b", "\\bserver.?error\\b", "\\binternal.?error\\b", "\\bprovider.?returned.?error\\b", "exceeded request buffer limit while retrying upstream", "\\bnetwork.?error\\b", "\\bconnection.?error\\b", "\\bconnection.?refused\\b", "\\bconnection.?lost\\b", "other side closed", "\\bfetch failed\\b", "\\bgetaddrinfo\\b", "\\bENOTFOUND\\b", "\\bEAI_AGAIN\\b", "\\bupstream.?connect", "reset before headers", "\\bsocket hang up\\b", "socket connection was closed", "\\btimed? ?out\\b", "\\bterminated\\b", "\\bwebsocket.?closed\\b", "\\bwebsocket.?error\\b", "\\bended without\\b", "stream ended before message_stop", "stream ended before a terminal response event", "http2 request did not get a response", "pending stream has been canceled", "you can retry your request", "try your request again", "please retry your request", "\\bResourceExhausted\\b", "\\bsubscription_sharing_usage_unavailable\\b", "\\bsubscription_sharing_user_unavailable\\b"])

# errors.rs TERMINAL_RATE_LIMIT
def sp_rx_terminal() -> String:
  "(?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing"

# errors.rs JS_DOT
def sp_rx_jsdot() -> String:
  "[^\\n\\r\\u{2028}\\u{2029}]"

# errors.rs RETRYABLE_TEXT: format!("(?i)rate{JS_DOT}?limit|overloaded|service{JS_DOT}?unavailable|upstream{JS_DOT}?connect|connection{JS_DOT}?refused")
def sp_rx_codex_retryable() -> String:
  String.concat(["(?i)rate", sp_rx_jsdot(), "?limit|overloaded|service", sp_rx_jsdot(), "?unavailable|upstream", sp_rx_jsdot(), "?connect|connection", sp_rx_jsdot(), "?refused"])

# errors.rs USAGE_LIMIT_CODE
def sp_rx_codex_usage() -> String:
  "(?i)usage_limit_reached|usage_not_included|rate_limit_exceeded"

# client.rs is_timeout_text TIMEOUT
def sp_rx_timeout() -> String:
  "(?i)timed? ?out"

# R2: the regex literal of each rule
def sp_regex(r: E.Rule) -> String:
  match r:
    case E.RLimit{}:
      sp_rx_limit()
    case E.RTransient{}:
      sp_rx_transient()
    case E.RCodexTerminal{}:
      sp_rx_terminal()
    case E.RCodexRetryable{}:
      sp_rx_codex_retryable()
    case E.RCodexUsage{}:
      sp_rx_codex_usage()
    case E.RTimeout{}:
      sp_rx_timeout()

# R2: the table of each rule: its regex literal read into phrases
def sp_table(r: E.Rule) -> List<&2, P.Ph>:
  rx_read(sp_regex(r))

# R1, R2: a phrase of the rule's table is found in the folded text
def sp_holds_text(r: E.Rule, text: String) -> Bool:
  Phrase.sp_any(TextPat.sp_fold(text), sp_table(r))

# R2: the rule holds for one of the texts
def sp_holds(+r: E.Rule, texts: List<&2, String>) -> Bool:
  match texts:
    case Nil{}:
      False{}
    case t <> more:
      Bool.or(sp_holds_text(r, t), sp_holds(r, more))

# R3: the spelling of a request and of its reply

def sp_w_rule(r: E.Rule, rest: String) -> String:
  match r:
    case E.RLimit{}:
      Wr.put_nat(0n, rest)
    case E.RTransient{}:
      Wr.put_nat(1n, rest)
    case E.RCodexTerminal{}:
      Wr.put_nat(2n, rest)
    case E.RCodexRetryable{}:
      Wr.put_nat(3n, rest)
    case E.RCodexUsage{}:
      Wr.put_nat(4n, rest)
    case E.RTimeout{}:
      Wr.put_nat(5n, rest)

def sp_w_req(q: FE.Req, rest: String) -> String:
  match q:
    case FE.Req{r, ts}:
      sp_w_rule(r, LawsBase.wire_spell_strs(ts, rest))

def sp_w_reply(q: FE.Req) -> String:
  match q:
    case FE.Req{r, ts}:
      Wr.put_bool(sp_holds(r, ts), "")

# every count and length of the request fits the wire
def sp_fit_req(q: FE.Req) -> Bool:
  match q:
    case FE.Req{r, ts}:
      LawsBase.wire_strs_fit(ts)

# Laws: the decision
# ------------------

# LAW err_text_regex (R1, R2): every rule holds for a list of texts
# exactly when one text, folded, holds a part that a phrase of the rule's
# table matches with its edges, the table read from the Rust regex
# literal the core replaced (sp_regex, quoted whole; rx_read: one phrase
# per way each alternative is taken); the search is laws/phrase.bend's
# (Phrase.sp_any), the fold laws/text_pat.bend's
# EXCLUDES: a phrase of the regex dropped, changed or moved to another
#   table, a phrase the regex does not have, an edge changed (a whole word
#   searched anywhere, a word start asked of the end), gap and jsgap
#   swapped, a case-sensitive search, a text of the list skipped, an empty
#   list read as a hit
law err_text_regex:
  for +r: E.Rule
  for +texts: List<&2, String>
  {E.holds(r, texts) == sp_holds(r, texts) : Bool}

# LAW err_text_found (R1, R2): a rule holds for every list of texts one of
# which, folded, holds a part that matches a phrase of the rule's table,
# its edges holding for the text before and after that part, whatever
# comes before and after it, in any case, and whatever the other texts are
# EXCLUDES: a phrase looked for only at the start or the end of a text,
#   text around the part that hides it, a case-sensitive search, a phrase
#   or a text of the list skipped
law err_text_found:
  for +r: E.Rule
  for +tp: List<&2, String>
  for +text: String
  for +tq: List<&2, String>
  for +a: String
  for +u: String
  for +b: String
  for +pre: List<&2, P.Ph>
  for +st: P.Edge
  for +its: List<&2, P.It>
  for +en: P.Edge
  for +post: List<&2, P.Ph>
  for hp: {sp_table(r) == List.append(&2, P.Ph, pre, P.Ph{st, its, en} <> post) : List<&2, P.Ph>}
  for hf: {TextPat.sp_fold(text) == String.append(a, String.append(u, b)) : String}
  for hu: {Phrase.sp_lang(u, its) == True{} : Bool}
  for hs: {Phrase.sp_start_ok(st, a) == True{} : Bool}
  for he: {Phrase.sp_end_ok(en, b) == True{} : Bool}
  {E.holds(r, List.append(&2, String, tp, text <> tq)) == True{} : Bool}

# LAW err_text_limit_example (R2): anchor: a quota message in another case,
# a retry delay with digits, one without
# EXCLUDES: a limit table that drifts from the regex it replaced
law err_text_limit_example:
  {[E.holds(E.RLimit{}, ["Quota exceeded"]), E.holds(E.RLimit{}, ["server requested 12s retry delay"]), E.holds(E.RLimit{}, ["server requested s retry delay"]), E.holds(E.RLimit{}, [])] == [True{}, True{}, False{}, False{}] : List<&2, Bool>}

# LAW err_text_transient_example (R1, R2): anchor: a status code alone and
# inside a longer number, a word start and a word continued before, a
# timeout word and a longer word, a folded Kelvin sign, a gap of one char
# and a line feed gap, the second text of a list
# EXCLUDES: a transient table that drifts from the regex it replaced
law err_text_transient_example:
  {[E.holds(E.RTransient{}, ["429"]), E.holds(E.RTransient{}, ["5242880"]), E.holds(E.RTransient{}, ["Overloaded"]), E.holds(E.RTransient{}, ["nonoverloaded"]), E.holds(E.RTransient{}, ["timeout_ms"]), E.holds(E.RTransient{}, ["Timed out"]), E.holds(E.RTransient{}, [SCon{'s', SCon{'o', SCon{'c', SCon{Chr{8490}, "et hang up"}}}}]), E.holds(E.RTransient{}, ["rate-limit"]), E.holds(E.RTransient{}, [SCon{'r', SCon{'a', SCon{'t', SCon{'e', SCon{'\n', "limit"}}}}}]), E.holds(E.RTransient{}, ["x", "529"])] == [True{}, False{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}, True{}] : List<&2, Bool>}

# LAW err_text_codex_terminal_example (R2): anchor: billing in another
# case; a limit phrase past the first eight
# EXCLUDES: a terminal table that drifts from the regex it replaced
law err_text_codex_terminal_example:
  {[E.holds(E.RCodexTerminal{}, ["Billing"]), E.holds(E.RCodexTerminal{}, ["provider admission queue is full"])] == [True{}, False{}] : List<&2, Bool>}

# LAW err_text_codex_retryable_example (R1, R2): anchor: a gap of one
# char, U+2028 and a carriage return refused as gaps, a word inside a word
# EXCLUDES: a retryable table that drifts from the regex it replaced (the
#   regex `.?` gap of the transient rule)
law err_text_codex_retryable_example:
  {[E.holds(E.RCodexRetryable{}, ["rate-limit"]), E.holds(E.RCodexRetryable{}, [SCon{'r', SCon{'a', SCon{'t', SCon{'e', SCon{Chr{8232}, "limit"}}}}}]), E.holds(E.RCodexRetryable{}, [SCon{'r', SCon{'a', SCon{'t', SCon{'e', SCon{'\r', "limit"}}}}}]), E.holds(E.RCodexRetryable{}, ["xoverloadedx"])] == [True{}, False{}, False{}, True{}] : List<&2, Bool>}

# LAW err_text_codex_usage_example (R1, R2): anchor: a code in capitals,
# a code with a space
# EXCLUDES: a usage table that drifts from the regex it replaced
law err_text_codex_usage_example:
  {[E.holds(E.RCodexUsage{}, ["USAGE_LIMIT_REACHED"]), E.holds(E.RCodexUsage{}, ["usage limit reached"])] == [True{}, False{}] : List<&2, Bool>}

# LAW err_text_timeout_example (R1, R2): anchor: `TimedOut` folded, a
# timeout inside a word, a bare `time`
# EXCLUDES: a timeout table that drifts from the regex it replaced
law err_text_timeout_example:
  {[E.holds(E.RTimeout{}, ["TimedOut"]), E.holds(E.RTimeout{}, ["timeout_ms"]), E.holds(E.RTimeout{}, ["time"])] == [True{}, True{}, False{}] : List<&2, Bool>}

# Laws: the entry (R3)
# --------------------

# LAW err_text_entry_decides (R3): a request spelled by the grammar, every
# count and length within the wire, is answered with the spelling of the
# spec's answer
# EXCLUDES: a rule read as another, a text lost or added, a default, a
#   reply spelled another way
law err_text_entry_decides:
  for +q: FE.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FE.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW err_text_entry_left_over (R3): input left over after a spelled
# request answers the error form
# EXCLUDES: trailing input ignored, or read as part of the request
law err_text_entry_left_over:
  for +q: FE.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FE.ffi(sp_w_req(q, rest)) == Wr.err("err_text: malformed request") : String}

# LAW err_text_entry_reads_only_requests (R3): an answer that is not the
# error form answers a request: the input is the spelling of a request
# that fits the wire, and the answer is the spec's answer to it
# EXCLUDES: a decoder that accepts an unknown rule, a short string, a
#   count or length past the wire or a missing field, and answers it
#   anyway (a default instead of the error form)
law err_text_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FE.ffi(s)) == False{} : Bool}
  exs q: FE.Req
  {(s, (sp_fit_req(q), FE.ffi(s))) == (sp_w_req(q, ""), (True{}, sp_w_reply(q))) : String & (Bool & String)}

# LAW err_text_entry_unknown_rule (R3): a rule tag past 5 is malformed,
# whatever follows
# EXCLUDES: an unknown rule read as a known one (exact error bytes)
law err_text_entry_unknown_rule:
  for +n: Nat
  for +rest: String
  {FE.ffi(Wr.put_nat(6n+n, rest)) == Wr.err("err_text: malformed request") : String}

# LAW err_text_entry_malformed_unless_request (R3): an input that does not
# begin with a spelled request that fits answers the malformed error: any
# other answer comes from an input that is a spelled request that fits,
# then possibly more
# EXCLUDES: another error text, or a reply, for input that holds no
#   request
law err_text_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(FE.ffi(s), Wr.err("err_text: malformed request")) == False{} : Bool}
  exs q: FE.Req
  exs rest: String
  {(s, sp_fit_req(q)) == (sp_w_req(q, rest), True{}) : String & Bool}

# LAW err_text_entry_example (R3): anchor: the wire strings Rust sends and
# the replies it reads; no texts, an unknown rule, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law err_text_entry_example:
  {[FE.ffi("0,1,14,Quota exceeded"), FE.ffi("1,2,1,x3,429"), FE.ffi("5,0,"), FE.ffi("6,0,"), FE.ffi("5,0,x")] == ["T", "T", "F", Wr.err("err_text: malformed request"), Wr.err("err_text: malformed request")] : List<&2, String>}

# LAW err_text_entry_premises_witness (R3): a request that fits exists, and
# so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law err_text_entry_premises_witness:
  {(sp_fit_req(FE.Req{E.RLimit{}, ["x"]}), FE.ffi("")) == (True{}, Wr.err("err_text: malformed request")) : Bool & String}
