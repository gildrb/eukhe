# stream_failure: the cause of a failed provider stream and the message a
# user reads for it (Rust: eukhe-ai utils/stream_failure.rs; laws:
# laws/stream_failure.bend). The cause comes from the provider's own
# error type (or the error's message when there is none) and the HTTP
# status; the message names the cause, the type and the status, the
# provider's short message and the request id. Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as Tp

# The cause of a stream failure (eukhe-types StreamFailureKind)
type Cause is Data:
  KRefusal{}
  KSafety{}
  KPayment{}
  KOverloaded{}
  KRateLimit{}
  KServer{}
  KAuth{}
  KPermission{}
  KInvalid{}
  KMalformed{}
  KDrop{}
  KStalled{}
  KRepeating{}
  KUnknown{}

# the content block a dropped stream was inside
type Block is Data:
  BThinking{}
  BText{}
  BToolCall{}
  BNone{}

# Patterns
# --------

# the chars of s, one item each, before rest
def lit(s: String, rest: List<&2, Tp.It>) -> List<&2, Tp.It>:
  match s:
    case SNil{}:
      rest
    case SCon{c, t}:
      Tp.One{Tp.CLit{c}} <> lit(t, rest)

def lits.go(xs: List<&2, String>) -> List<&2, List<&2, Tp.It>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      lit(x, []) <> lits.go(t)

# whether some needle is in t
def has(+t: String, xs: List<&2, String>) -> Bool:
  Tp.hit(t, Tp.Pat{False{}, lits.go(xs)})

# sensitive|safety|prohibited_content|blocklist|spii|recitation|
# content.?filter|guardrail|flagged
def safety_pat() -> Tp.Pat:
  Tp.Pat{False{}, [lit("sensitive", []), lit("safety", []), lit("prohibited_content", []), lit("blocklist", []), lit("spii", []), lit("recitation", []), lit("contentfilter", []), lit("content", Tp.One{Tp.CAny{}} <> lit("filter", [])), lit("guardrail", []), lit("flagged", [])]}

# permission|forbidden|access.?denied
def permission_pat() -> Tp.Pat:
  Tp.Pat{False{}, [lit("permission", []), lit("forbidden", []), lit("accessdenied", []), lit("access", Tp.One{Tp.CAny{}} <> lit("denied", []))]}

# Classification
# --------------

def is_status(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Nat.is_eq(s, n)

def is_5xx(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Nat.is_le(500n, s)

# a test and the cause it gives
type Test is Data:
  Test{hit: Bool, cause: Cause}

# the cause of the first test that holds, else d
def first(cs: List<&2, Test>, d: Cause) -> Cause:
  match cs:
    case Nil{}:
      d
    case c <> rest:
      match c:
        case Test{b, k}:
          match b:
            case True{}:
              k
            case False{}:
              first(rest, d)

# the cause for the lowered type t and the status, in the order of the
# Rust it replaced: a 402 is a payment failure whatever the type (credits
# do not refill inside a retry ladder); permission and 403 shapes are
# entitlement or policy denials, never stale credentials
def classify.go(+t: String, +st: Maybe<&2, Nat>) -> Cause:
  first([
    Test{is_status(st, 402n), KPayment{}},
    Test{String.eq(t, "refusal"), KRefusal{}},
    Test{Tp.hit(t, safety_pat()), KSafety{}},
    Test{Bool.or(has(t, ["overloaded"]), is_status(st, 529n)), KOverloaded{}},
    Test{Bool.or(has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), is_status(st, 429n)), KRateLimit{}},
    Test{Bool.or(has(t, ["authentication", "unauthorized"]), is_status(st, 401n)), KAuth{}},
    Test{Bool.or(Tp.hit(t, permission_pat()), is_status(st, 403n)), KPermission{}},
    Test{Bool.or(has(t, ["invalid_request", "not_found_error"]), Bool.or(is_status(st, 400n), is_status(st, 404n))), KInvalid{}},
    Test{has(t, ["malformed"]), KMalformed{}},
    Test{Bool.or(has(t, ["api_error", "server_error", "unavailable"]), is_5xx(st)), KServer{}}
  ], KUnknown{})

# the cause of a failure of the provider error type t (None: none) and the
# HTTP status; the type is searched lowered (bend/text_pat.bend `lower`)
def classify(t: Maybe<&2, String>, +st: Maybe<&2, Nat>) -> Cause:
  match t:
    case None{}:
      classify.go("", st)
    case Some{x}:
      classify.go(Tp.lower(x), st)

# Messages
# --------

def kind_text(k: Cause) -> String:
  match k:
    case KRefusal{}:
      "Model refused to respond"
    case KSafety{}:
      "Response blocked by provider safety filters"
    case KPayment{}:
      "Provider requires payment"
    case KOverloaded{}:
      "Provider overloaded"
    case KRateLimit{}:
      "Provider rate limit exceeded"
    case KServer{}:
      "Provider server error"
    case KAuth{}:
      "Provider authentication failed"
    case KPermission{}:
      "Provider denied access to the requested resource"
    case KInvalid{}:
      "Provider rejected the request"
    case KMalformed{}:
      "Provider returned a malformed response"
    case KDrop{}:
      "Provider dropped the response stream"
    case KStalled{}:
      "Provider stream stalled"
    case KRepeating{}:
      "Provider stream repeating"
    case KUnknown{}:
      "Provider stream failed"

def quals.status(st: Maybe<&2, Nat>) -> List<&2, String>:
  match st:
    case None{}:
      []
    case Some{s}:
      [Nat.show(s)]

# the qualifiers: the provider error type, then the status
def quals(t: Maybe<&2, String>, st: Maybe<&2, Nat>) -> List<&2, String>:
  match t:
    case None{}:
      quals.status(st)
    case Some{x}:
      x <> quals.status(st)

def message.quals(qs: List<&2, String>) -> String:
  match qs:
    case Nil{}:
      ""
    case q <> rest:
      String.concat([" (", String.join(q <> rest, ", "), ")"])

def message.detail(d: Maybe<&2, String>) -> String:
  match d:
    case None{}:
      ""
    case Some{x}:
      String.append(": ", x)

def message.rid(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      ""
    case Some{x}:
      String.concat([" [request_id: ", x, "]"])

# "Provider overloaded (overloaded_error, 529): <detail> [request_id: <id>]"
def message(k: Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> String:
  String.concat([kind_text(k), message.quals(quals(t, st)), message.detail(d), message.rid(r)])

# HTTP errors
# -----------

def or_else(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

# whether only a structured type may give this cause
def needs_type(k: Cause) -> Bool:
  match k:
    case KAuth{}:
      True{}
    case KPermission{}:
      True{}
    case KRefusal{}:
      False{}
    case KSafety{}:
      False{}
    case KPayment{}:
      False{}
    case KOverloaded{}:
      False{}
    case KRateLimit{}:
      False{}
    case KServer{}:
      False{}
    case KInvalid{}:
      False{}
    case KMalformed{}:
      False{}
    case KDrop{}:
      False{}
    case KStalled{}:
      False{}
    case KRepeating{}:
      False{}
    case KUnknown{}:
      False{}

def is_none(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def http.kind(k: Cause, retry: Bool, +st: Maybe<&2, Nat>) -> Cause:
  match retry:
    case True{}:
      classify(None{}, st)
    case False{}:
      k

def http.msg(k: Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match k:
    case KUnknown{}:
      None{}
    case KRefusal{}:
      Some{message(KRefusal{}, t, st, d, r)}
    case KSafety{}:
      Some{message(KSafety{}, t, st, d, r)}
    case KPayment{}:
      Some{message(KPayment{}, t, st, d, r)}
    case KOverloaded{}:
      Some{message(KOverloaded{}, t, st, d, r)}
    case KRateLimit{}:
      Some{message(KRateLimit{}, t, st, d, r)}
    case KServer{}:
      Some{message(KServer{}, t, st, d, r)}
    case KAuth{}:
      Some{message(KAuth{}, t, st, d, r)}
    case KPermission{}:
      Some{message(KPermission{}, t, st, d, r)}
    case KInvalid{}:
      Some{message(KInvalid{}, t, st, d, r)}
    case KMalformed{}:
      Some{message(KMalformed{}, t, st, d, r)}
    case KDrop{}:
      Some{message(KDrop{}, t, st, d, r)}
    case KStalled{}:
      Some{message(KStalled{}, t, st, d, r)}
    case KRepeating{}:
      Some{message(KRepeating{}, t, st, d, r)}

# The cause of an HTTP error
type Http is Data:
  Http{kind: Cause, ptype: Maybe<&2, String>, msg: Maybe<&2, String>}

def http.of(+k: Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Http:
  Http{k, t, http.msg(k, t, st, d, r)}

# an HTTP error with its message `m`, status, body error type and message,
# the error's own code and its SDK class name, and the request id: the
# provider error type is the body's, else the code, else the class name;
# the cause comes from that type (else the message), but an auth or
# permission cause read from the message alone comes from the status
# alone; the user's message (None: the raw message stays) names it
def http(m: String, +st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, code: Maybe<&2, String>, sdk: Maybe<&2, String>, r: Maybe<&2, String>) -> Http:
  +t = or_else(bt, or_else(code, sdk))
  +k = classify(or_else(t, Some{m}), st)
  http.of(http.kind(k, Bool.and(needs_type(k), is_none(t)), st), t, st, d, r)

# Stream ends
# -----------

# A failure the core names
type Named is Data:
  Named{kind: Cause, msg: String}

def from_stop.of(+k: Cause, raw: String, r: Maybe<&2, String>) -> Named:
  Named{k, message(k, Some{raw}, None{}, None{}, r)}

# a stream that ended with the provider stop reason `raw` (None: none)
# that maps to an error
def from_stop(raw: Maybe<&2, String>, r: Maybe<&2, String>) -> Named:
  match raw:
    case None{}:
      Named{KUnknown{}, message(KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r)}
    case Some{+x}:
      from_stop.of(classify(Some{x}, None{}), x, r)

def drop.detail(b: Block) -> String:
  match b:
    case BThinking{}:
      "the stream ended inside a thinking block before the stop signal"
    case BText{}:
      "the stream ended inside a text block before the stop signal"
    case BToolCall{}:
      "the stream ended inside a tool-call block before the stop signal"
    case BNone{}:
      "the stream ended before any response content or stop signal"

# a stream the provider ended mid-block without its terminal marker
def drop(b: Block) -> String:
  message(KDrop{}, Some{"stream_drop"}, None{}, Some{drop.detail(b)}, None{})

# a stream with no event for `ms` (the deadline, as the host writes it)
def stalled(ms: String) -> String:
  message(KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})

# the chars of a repeated line a message shows: up to 80, then ...
def shown.go(s: String, n: Nat) -> String:
  match s n:
    case SNil{} _:
      SNil{}
    case SCon{c, t} 0n:
      SCon{Chr{8230}, SNil{}}
    case SCon{c, t} 1n+m:
      SCon{c, shown.go(t, m)}

def shown(s: String) -> String:
  shown.go(s, 80n)

# The failure of a stream the repetition guard cut
type Repeat is Data:
  Repeat{msg: String, period: Nat}

def repeating.detail(+limit: Nat, period: Nat, q: String) -> String:
  match period:
    case 0n:
      String.concat(["the same line ", Nat.show(limit), " times in a row: ", q])
    case 1n:
      String.concat(["the same line ", Nat.show(limit), " times in a row: ", q])
    case 2n+p:
      String.concat(["a cycle of ", Nat.show(2n+p), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q])

def repeating.period(p: Nat) -> Nat:
  match p:
    case 0n:
      1n
    case 1n+q:
      1n+q

# the last `limit` output lines repeat with a period of `period` lines (0
# and 1: one line); q is the shown line, quoted by the host; the period
# recorded is at least 1
def repeating(+limit: Nat, +period: Nat, q: String) -> Repeat:
  Repeat{message(KRepeating{}, None{}, None{}, Some{repeating.detail(limit, period, q)}, None{}), repeating.period(period)}
