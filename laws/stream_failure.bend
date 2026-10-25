# eukhe: the laws of area stream_failure

import Base
import ../bend/stream_failure.bend as Sf
import ../bend/ffi_stream_failure.bend as FSf
import ../bend/text_pat.bend as Tp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./text_pat.bend as TextPat
import ./overflow.bend as OverflowLaws

# (F1) The cause of a failed provider stream and its message
# ----------------------------------------------------------
# bend/stream_failure.bend, run as the compiled core by
# bend/ffi_stream_failure.bend (eukhe-bend rules/stream_failure.rs; asked
# by eukhe-ai utils/stream_failure.rs for every provider error it
# classifies or reports). Every input is free. The search for a needle is
# pinned by laws/text_pat.bend (text_pat_any, text_pat_hit, text_pat_search_*;
# text_pat_lower: the lowering).
#
# R1: the cause of a provider error type t (when there is none, the text
#     the caller gives instead; neither: the empty text) and a status, the
#     type lowered (text_pat_lower), is the first that holds of: status
#     402: payment required; the type is "refusal": refusal; sensitive,
#     safety, prohibited_content, blocklist, spii, recitation,
#     content<any one char or none, not a line feed>filter, guardrail or
#     flagged in it: safety; overloaded in it or status 529: overloaded;
#     rate_limit, usage_limit, usage_not_included or throttl in it or
#     status 429: rate limit; authentication or unauthorized in it or
#     status 401: auth; permission, forbidden or access<one char or
#     none>denied in it or status 403: permission; invalid_request or
#     not_found_error in it or status 400 or 404: invalid request;
#     malformed in it: malformed response; api_error, server_error or
#     unavailable in it or a status of 500 or more: server error; else
#     unknown.
# R2: a message is the cause's text, then " (" the provider error type
#     and the status joined by ", " ")" when there is either, then ": "
#     and the detail when there is one, then " [request_id: " the id "]"
#     when there is one. The texts: refusal "Model refused to respond",
#     safety "Response blocked by provider safety filters", payment
#     "Provider requires payment", overloaded "Provider overloaded", rate
#     limit "Provider rate limit exceeded", server "Provider server
#     error", auth "Provider authentication failed", permission "Provider
#     denied access to the requested resource", invalid "Provider
#     rejected the request", malformed "Provider returned a malformed
#     response", drop "Provider dropped the response stream", stalled
#     "Provider stream stalled", repeating "Provider stream repeating",
#     unknown "Provider stream failed".
# R3: an HTTP error's provider error type is the body's error type, else
#     the error's own code, else its SDK class name; its cause is R1's for
#     that type (when none, for the error's message) and its status, but
#     an auth or permission cause read without a type is R1's for the
#     status alone; an unknown cause keeps the raw message (none), any
#     other gives the R2 message with the body's message as detail and the
#     request id.
# R4: a stream that ended with an error stop reason: with a reason, R1's
#     cause of the reason as the type (no status) and the R2 message with
#     the reason as type; with none, unknown and the R2 message with the
#     detail "stream ended with an error and no stop reason". A dropped
#     stream: the R2 drop message with type "stream_drop" and the detail
#     of its open block. A stalled stream: the R2 stalled message with the
#     detail "no stream event for <ms>ms" (ms as the host writes it). A
#     repeated line shows its first 80 chars and U+2026 when it is longer,
#     else whole. A repeating stream: the R2 repeating message with the
#     detail "the same line <limit> times in a row: <q>" for a period of 0
#     or 1, else "a cycle of <period> lines repeated over the last <limit>
#     lines, ending with <q>" (q quoted by the host); the period recorded
#     is the period, at least 1.
# R5: the entry answers each request Rust writes (every number, length
#     and count within the wire) with the answer of R1-R4, reads exactly
#     the request and nothing after it, and answers any other input with
#     the exact error form `E stream_failure: malformed request`.

# Spec helpers
# ------------

def sp_pick(b: Bool, k: Sf.Cause, other: Sf.Cause) -> Sf.Cause:
  match b:
    case True{}:
      k
    case False{}:
      other

def sp_st(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Nat.is_eq(s, n)

def sp_st5(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Nat.is_le(500n, s)

# R1: whether one of the needles xs is in t
def sp_has(+t: String, xs: List<&2, String>) -> Bool:
  TextPat.sp_any(t, [Tp.Pat{False{}, OverflowLaws.sp_lits(xs)}])

# R1: content.?filter and access.?denied, with their literal neighbours
def sp_safety() -> Tp.Pat:
  Tp.Pat{False{}, [OverflowLaws.sp_s("sensitive", []), OverflowLaws.sp_s("safety", []), OverflowLaws.sp_s("prohibited_content", []), OverflowLaws.sp_s("blocklist", []), OverflowLaws.sp_s("spii", []), OverflowLaws.sp_s("recitation", []), OverflowLaws.sp_s("contentfilter", []), OverflowLaws.sp_s("content", Tp.One{Tp.CAny{}} <> OverflowLaws.sp_s("filter", [])), OverflowLaws.sp_s("guardrail", []), OverflowLaws.sp_s("flagged", [])]}

def sp_permission() -> Tp.Pat:
  Tp.Pat{False{}, [OverflowLaws.sp_s("permission", []), OverflowLaws.sp_s("forbidden", []), OverflowLaws.sp_s("accessdenied", []), OverflowLaws.sp_s("access", Tp.One{Tp.CAny{}} <> OverflowLaws.sp_s("denied", []))]}

# R1: the cause of the lowered type t
def sp_cause(+t: String, +st: Maybe<&2, Nat>) -> Sf.Cause:
  sp_pick(sp_st(st, 402n), Sf.KPayment{}, sp_pick(String.eq(t, "refusal"), Sf.KRefusal{}, sp_pick(TextPat.sp_any(t, [sp_safety()]), Sf.KSafety{}, sp_pick(Bool.or(sp_has(t, ["overloaded"]), sp_st(st, 529n)), Sf.KOverloaded{}, sp_pick(Bool.or(sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), sp_st(st, 429n)), Sf.KRateLimit{}, sp_pick(Bool.or(sp_has(t, ["authentication", "unauthorized"]), sp_st(st, 401n)), Sf.KAuth{}, sp_pick(Bool.or(TextPat.sp_any(t, [sp_permission()]), sp_st(st, 403n)), Sf.KPermission{}, sp_pick(Bool.or(sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(sp_st(st, 400n), sp_st(st, 404n))), Sf.KInvalid{}, sp_pick(sp_has(t, ["malformed"]), Sf.KMalformed{}, sp_pick(Bool.or(sp_has(t, ["api_error", "server_error", "unavailable"]), sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}))))))))))

# R1: the cause of a type (None: none) and a status
def sp_classify(t: Maybe<&2, String>, +st: Maybe<&2, Nat>) -> Sf.Cause:
  match t:
    case None{}:
      sp_cause("", st)
    case Some{x}:
      sp_cause(TextPat.sp_lower(x), st)

# R2: the texts of the causes
def sp_text(k: Sf.Cause) -> String:
  match k:
    case Sf.KRefusal{}:
      "Model refused to respond"
    case Sf.KSafety{}:
      "Response blocked by provider safety filters"
    case Sf.KPayment{}:
      "Provider requires payment"
    case Sf.KOverloaded{}:
      "Provider overloaded"
    case Sf.KRateLimit{}:
      "Provider rate limit exceeded"
    case Sf.KServer{}:
      "Provider server error"
    case Sf.KAuth{}:
      "Provider authentication failed"
    case Sf.KPermission{}:
      "Provider denied access to the requested resource"
    case Sf.KInvalid{}:
      "Provider rejected the request"
    case Sf.KMalformed{}:
      "Provider returned a malformed response"
    case Sf.KDrop{}:
      "Provider dropped the response stream"
    case Sf.KStalled{}:
      "Provider stream stalled"
    case Sf.KRepeating{}:
      "Provider stream repeating"
    case Sf.KUnknown{}:
      "Provider stream failed"

# R2: the qualifiers, parenthesized
def sp_quals(t: Maybe<&2, String>, st: Maybe<&2, Nat>) -> String:
  match t st:
    case None{} None{}:
      ""
    case Some{x} None{}:
      String.concat([" (", x, ")"])
    case None{} Some{s}:
      String.concat([" (", Nat.show(s), ")"])
    case Some{x} Some{s}:
      String.concat([" (", x, ", ", Nat.show(s), ")"])

def sp_after(open: String, m: Maybe<&2, String>, close: String) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      String.concat([open, x, close])

# R2: the message
def sp_message(k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> String:
  String.concat([sp_text(k), sp_quals(t, st), sp_after(": ", d, ""), sp_after(" [request_id: ", r, "]")])

def sp_or(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

def sp_typeless(t: Maybe<&2, String>, k: Sf.Cause) -> Bool:
  match t:
    case Some{x}:
      False{}
    case None{}:
      match k:
        case Sf.KAuth{}:
          True{}
        case Sf.KPermission{}:
          True{}
        case Sf.KRefusal{}:
          False{}
        case Sf.KSafety{}:
          False{}
        case Sf.KPayment{}:
          False{}
        case Sf.KOverloaded{}:
          False{}
        case Sf.KRateLimit{}:
          False{}
        case Sf.KServer{}:
          False{}
        case Sf.KInvalid{}:
          False{}
        case Sf.KMalformed{}:
          False{}
        case Sf.KDrop{}:
          False{}
        case Sf.KStalled{}:
          False{}
        case Sf.KRepeating{}:
          False{}
        case Sf.KUnknown{}:
          False{}

def sp_unknown(k: Sf.Cause) -> Bool:
  match k:
    case Sf.KUnknown{}:
      True{}
    case Sf.KRefusal{}:
      False{}
    case Sf.KSafety{}:
      False{}
    case Sf.KPayment{}:
      False{}
    case Sf.KOverloaded{}:
      False{}
    case Sf.KRateLimit{}:
      False{}
    case Sf.KServer{}:
      False{}
    case Sf.KAuth{}:
      False{}
    case Sf.KPermission{}:
      False{}
    case Sf.KInvalid{}:
      False{}
    case Sf.KMalformed{}:
      False{}
    case Sf.KDrop{}:
      False{}
    case Sf.KStalled{}:
      False{}
    case Sf.KRepeating{}:
      False{}

def sp_http.msg(u: Bool, k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match u:
    case True{}:
      None{}
    case False{}:
      Some{sp_message(k, t, st, d, r)}

def sp_http.of(+k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Sf.Http:
  Sf.Http{k, t, sp_http.msg(sp_unknown(k), k, t, st, d, r)}

def sp_http.cause(b: Bool, k: Sf.Cause, +st: Maybe<&2, Nat>) -> Sf.Cause:
  match b:
    case True{}:
      sp_classify(None{}, st)
    case False{}:
      k

# R3: an HTTP error
def sp_http(m: String, +st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, code: Maybe<&2, String>, sdk: Maybe<&2, String>, r: Maybe<&2, String>) -> Sf.Http:
  +t = sp_or(bt, sp_or(code, sdk))
  +k = sp_classify(sp_or(t, Some{m}), st)
  sp_http.of(sp_http.cause(sp_typeless(t, k), k, st), t, st, d, r)

# R4: a stream that ended with an error stop reason
def sp_from_stop(raw: Maybe<&2, String>, r: Maybe<&2, String>) -> Sf.Named:
  match raw:
    case None{}:
      Sf.Named{Sf.KUnknown{}, sp_message(Sf.KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r)}
    case Some{+x}:
      +k = sp_classify(Some{x}, None{})
      Sf.Named{k, sp_message(k, Some{x}, None{}, None{}, r)}

# R4: the detail of a dropped stream, by its open block
def sp_drop_detail(b: Sf.Block) -> String:
  match b:
    case Sf.BThinking{}:
      "the stream ended inside a thinking block before the stop signal"
    case Sf.BText{}:
      "the stream ended inside a text block before the stop signal"
    case Sf.BToolCall{}:
      "the stream ended inside a tool-call block before the stop signal"
    case Sf.BNone{}:
      "the stream ended before any response content or stop signal"

def sp_shown.pick(short: Bool, +s: String) -> String:
  match short:
    case True{}:
      s
    case False{}:
      String.append(String.take(s, 80n), SCon{Chr{8230}, SNil{}})

# R4: a repeated line as a message shows it
def sp_shown(+s: String) -> String:
  sp_shown.pick(Nat.is_le(String.length(s), 80n), s)

def sp_repeat_detail(b: Bool, +limit: Nat, +period: Nat, q: String) -> String:
  match b:
    case True{}:
      String.concat(["the same line ", Nat.show(limit), " times in a row: ", q])
    case False{}:
      String.concat(["a cycle of ", Nat.show(period), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q])

# R4: a repeating stream
def sp_repeating(+limit: Nat, +period: Nat, q: String) -> Sf.Repeat:
  Sf.Repeat{sp_message(Sf.KRepeating{}, None{}, None{}, Some{sp_repeat_detail(Nat.is_le(period, 1n), limit, period, q)}, None{}), Nat.max(period, 1n)}

# R5: the spelling of a request and of its reply

def sp_w_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def sp_w_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

def sp_w_cause(k: Sf.Cause, rest: String) -> String:
  match k:
    case Sf.KRefusal{}:
      Wr.put_nat(0n, rest)
    case Sf.KSafety{}:
      Wr.put_nat(1n, rest)
    case Sf.KPayment{}:
      Wr.put_nat(2n, rest)
    case Sf.KOverloaded{}:
      Wr.put_nat(3n, rest)
    case Sf.KRateLimit{}:
      Wr.put_nat(4n, rest)
    case Sf.KServer{}:
      Wr.put_nat(5n, rest)
    case Sf.KAuth{}:
      Wr.put_nat(6n, rest)
    case Sf.KPermission{}:
      Wr.put_nat(7n, rest)
    case Sf.KInvalid{}:
      Wr.put_nat(8n, rest)
    case Sf.KMalformed{}:
      Wr.put_nat(9n, rest)
    case Sf.KDrop{}:
      Wr.put_nat(10n, rest)
    case Sf.KStalled{}:
      Wr.put_nat(11n, rest)
    case Sf.KRepeating{}:
      Wr.put_nat(12n, rest)
    case Sf.KUnknown{}:
      Wr.put_nat(13n, rest)

def sp_w_block(b: Sf.Block, rest: String) -> String:
  match b:
    case Sf.BThinking{}:
      Wr.put_nat(0n, rest)
    case Sf.BText{}:
      Wr.put_nat(1n, rest)
    case Sf.BToolCall{}:
      Wr.put_nat(2n, rest)
    case Sf.BNone{}:
      Wr.put_nat(3n, rest)

def sp_fit_mstr(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(String.length(x))

def sp_fit_mnat(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(x)

def sp_w_req(q: FSf.Req, rest: String) -> String:
  match q:
    case FSf.QClassify{t, st}:
      Wr.put_nat(0n, sp_w_mstr(t, sp_w_mnat(st, rest)))
    case FSf.QMessage{k, t, st, d, r}:
      Wr.put_nat(1n, sp_w_cause(k, sp_w_mstr(t, sp_w_mnat(st, sp_w_mstr(d, sp_w_mstr(r, rest))))))
    case FSf.QHttp{m, st, bt, d, code, sdk, r}:
      Wr.put_nat(2n, Wr.put_str(m, sp_w_mnat(st, sp_w_mstr(bt, sp_w_mstr(d, sp_w_mstr(code, sp_w_mstr(sdk, sp_w_mstr(r, rest))))))))
    case FSf.QFromStop{raw, r}:
      Wr.put_nat(3n, sp_w_mstr(raw, sp_w_mstr(r, rest)))
    case FSf.QDrop{b}:
      Wr.put_nat(4n, sp_w_block(b, rest))
    case FSf.QStalled{ms}:
      Wr.put_nat(5n, Wr.put_str(ms, rest))
    case FSf.QShown{line}:
      Wr.put_nat(6n, Wr.put_str(line, rest))
    case FSf.QRepeating{limit, period, q}:
      Wr.put_nat(7n, Wr.put_nat(limit, Wr.put_nat(period, Wr.put_str(q, rest))))

def sp_w_http(h: Sf.Http) -> String:
  match h:
    case Sf.Http{k, t, msg}:
      sp_w_cause(k, sp_w_mstr(t, sp_w_mstr(msg, "")))

def sp_w_named(n: Sf.Named) -> String:
  match n:
    case Sf.Named{k, msg}:
      sp_w_cause(k, Wr.put_str(msg, ""))

def sp_w_repeat(x: Sf.Repeat) -> String:
  match x:
    case Sf.Repeat{msg, p}:
      Wr.put_str(msg, Wr.put_nat(p, ""))

def sp_w_reply(q: FSf.Req) -> String:
  match q:
    case FSf.QClassify{t, st}:
      sp_w_cause(sp_classify(t, st), "")
    case FSf.QMessage{k, t, st, d, r}:
      Wr.put_str(sp_message(k, t, st, d, r), "")
    case FSf.QHttp{m, st, bt, d, code, sdk, r}:
      sp_w_http(sp_http(m, st, bt, d, code, sdk, r))
    case FSf.QFromStop{raw, r}:
      sp_w_named(sp_from_stop(raw, r))
    case FSf.QDrop{b}:
      Wr.put_str(sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{sp_drop_detail(b)}, None{}), "")
    case FSf.QStalled{ms}:
      Wr.put_str(sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{}), "")
    case FSf.QShown{line}:
      Wr.put_str(sp_shown(line), "")
    case FSf.QRepeating{limit, period, q}:
      sp_w_repeat(sp_repeating(limit, period, q))

# every number and length of the request fits the wire
def sp_fit_req(q: FSf.Req) -> Bool:
  match q:
    case FSf.QClassify{t, st}:
      Bool.and(sp_fit_mstr(t), sp_fit_mnat(st))
    case FSf.QMessage{k, t, st, d, r}:
      Bool.and(sp_fit_mstr(t), Bool.and(sp_fit_mnat(st), Bool.and(sp_fit_mstr(d), sp_fit_mstr(r))))
    case FSf.QHttp{m, st, bt, d, code, sdk, r}:
      Bool.and(LawsBase.wire_fits(String.length(m)), Bool.and(sp_fit_mnat(st), Bool.and(sp_fit_mstr(bt), Bool.and(sp_fit_mstr(d), Bool.and(sp_fit_mstr(code), Bool.and(sp_fit_mstr(sdk), sp_fit_mstr(r)))))))
    case FSf.QFromStop{raw, r}:
      Bool.and(sp_fit_mstr(raw), sp_fit_mstr(r))
    case FSf.QDrop{b}:
      True{}
    case FSf.QStalled{ms}:
      LawsBase.wire_fits(String.length(ms))
    case FSf.QShown{line}:
      LawsBase.wire_fits(String.length(line))
    case FSf.QRepeating{limit, period, q}:
      Bool.and(LawsBase.wire_fits(limit), Bool.and(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q))))

# Laws: the causes and messages
# -----------------------------

# LAW stream_failure_classify (R1): the cause of every provider error type
# (or none) and every status is the spec's
# EXCLUDES: a test out of order (a 402 read from the type, a rate limit
#   before the overload), a needle dropped or changed, a type searched
#   without lowering, `.?` that takes two chars or a line feed, a status
#   compared wrongly
law stream_failure_classify:
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  {Sf.classify(t, st) == sp_classify(t, st) : Sf.Cause}

# LAW stream_failure_message (R2): the message of every cause, type,
# status, detail and request id is the spec's
# EXCLUDES: a qualifier dropped, swapped or doubled, another separator, a
#   cause's text changed, the request id before the detail
law stream_failure_message:
  for +k: Sf.Cause
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  for +d: Maybe<&2, String>
  for +r: Maybe<&2, String>
  {Sf.message(k, t, st, d, r) == sp_message(k, t, st, d, r) : String}

# LAW stream_failure_http (R3): the cause, type and message of every HTTP
# error are the spec's
# EXCLUDES: another precedence of the type, the message searched when a
#   type exists, an auth cause read from message text, a message for an
#   unknown cause, the body's message dropped from the detail
law stream_failure_http:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +bt: Maybe<&2, String>
  for +d: Maybe<&2, String>
  for +code: Maybe<&2, String>
  for +sdk: Maybe<&2, String>
  for +r: Maybe<&2, String>
  {Sf.http(m, st, bt, d, code, sdk, r) == sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}

# LAW stream_failure_from_stop (R4): the cause and message of every
# stream that ended with an error stop reason (or none) are the spec's
# EXCLUDES: a reason classified with a status, a message without the
#   reason, another text for a missing reason
law stream_failure_from_stop:
  for +raw: Maybe<&2, String>
  for +r: Maybe<&2, String>
  {Sf.from_stop(raw, r) == sp_from_stop(raw, r) : Sf.Named}

# LAW stream_failure_ends (R4): the messages of every dropped and stalled
# stream are the spec's
# EXCLUDES: another detail per block, a drop without its type, a stall
#   without its deadline
law stream_failure_ends:
  for +b: Sf.Block
  for +ms: String
  {(Sf.drop(b), Sf.stalled(ms)) == (sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{sp_drop_detail(b)}, None{}), sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : String & String}

# LAW stream_failure_shown (R4): every repeated line shows as the spec
# says: its first 80 chars and U+2026 when longer, else whole
# EXCLUDES: a cut at 79 or 81 chars, a cut line without the mark, a mark
#   on a line of exactly 80 chars
law stream_failure_shown:
  for +s: String
  {Sf.shown(s) == sp_shown(s) : String}

# LAW stream_failure_repeating (R4): the message and period of every
# repeating stream are the spec's
# EXCLUDES: a cycle of one line read as a cycle, a period of 0 recorded,
#   the limit and the period swapped in the text
law stream_failure_repeating:
  for +limit: Nat
  for +period: Nat
  for +q: String
  {Sf.repeating(limit, period, q) == sp_repeating(limit, period, q) : Sf.Repeat}

# LAW stream_failure_example (R1-R4): anchor: the vectors of the Rust
# tests: classification by type and status (a 402 before the type), the
# messages with and without qualifiers, the stop reasons
# EXCLUDES: a spec that drifts from the Rust it replaced
law stream_failure_example:
  {([Sf.classify(Some{"refusal"}, None{}), Sf.classify(Some{"SAFETY"}, None{}), Sf.classify(Some{"overloaded_error"}, None{}), Sf.classify(Some{"other"}, Some{529n}), Sf.classify(Some{"rate_limit_error"}, None{}), Sf.classify(Some{"usage_not_included"}, None{}), Sf.classify(Some{"authentication_error"}, None{}), Sf.classify(Some{"forbidden"}, None{}), Sf.classify(Some{"invalid_request_error"}, None{}), Sf.classify(Some{"api_error"}, None{}), Sf.classify(Some{"other"}, Some{503n}), Sf.classify(Some{"weird"}, None{}), Sf.classify(Some{"invalid_request_error"}, Some{402n}), Sf.classify(None{}, Some{402n}), Sf.classify(Some{"Content-Filter"}, None{})], ([Sf.message(Sf.KOverloaded{}, Some{"overloaded_error"}, Some{529n}, Some{"slow down"}, Some{"req_abc"}), Sf.message(Sf.KInvalid{}, None{}, Some{400n}, None{}, None{})], [Sf.from_stop(Some{"refusal"}, None{}), Sf.from_stop(None{}, None{})])) == ([Sf.KRefusal{}, Sf.KSafety{}, Sf.KOverloaded{}, Sf.KOverloaded{}, Sf.KRateLimit{}, Sf.KRateLimit{}, Sf.KAuth{}, Sf.KPermission{}, Sf.KInvalid{}, Sf.KServer{}, Sf.KServer{}, Sf.KUnknown{}, Sf.KPayment{}, Sf.KPayment{}, Sf.KSafety{}], (["Provider overloaded (overloaded_error, 529): slow down [request_id: req_abc]", "Provider rejected the request (400)"], [Sf.Named{Sf.KRefusal{}, "Model refused to respond (refusal)"}, Sf.Named{Sf.KUnknown{}, "Provider stream failed: stream ended with an error and no stop reason"}])) : List<&2, Sf.Cause> & (List<&2, String> & List<&2, Sf.Named>)}

# LAW stream_failure_http_example (R3): anchor: a body type, an SDK class
# name standing in for the type, an auth word in a message without a type
# (the status decides), an unknown cause keeping the raw message
# EXCLUDES: a precedence or fallback that drifts from the Rust
law stream_failure_http_example:
  {[Sf.http("429 x", Some{429n}, None{}, Some{"slow"}, None{}, Some{"ApiError"}, None{}), Sf.http("unauthorized here", Some{400n}, None{}, None{}, None{}, None{}, Some{"r1"}), Sf.http("odd", None{}, None{}, None{}, None{}, None{}, None{}), Sf.http("x", Some{500n}, Some{"overloaded_error"}, Some{"busy"}, Some{"c"}, None{}, None{})] == [Sf.Http{Sf.KRateLimit{}, Some{"ApiError"}, Some{"Provider rate limit exceeded (ApiError, 429): slow"}}, Sf.Http{Sf.KInvalid{}, None{}, Some{"Provider rejected the request (400) [request_id: r1]"}}, Sf.Http{Sf.KUnknown{}, None{}, None{}}, Sf.Http{Sf.KOverloaded{}, Some{"overloaded_error"}, Some{"Provider overloaded (overloaded_error, 500): busy"}}] : List<&2, Sf.Http>}

# Laws: the entry (R5)
# --------------------

# LAW stream_failure_entry_answers (R5): the entry answers every request
# Rust spells, every number and length within the wire, with the spelled
# answer of the spec
# EXCLUDES: the questions swapped, the fields read in another order, a
#   cause or block read as another, a default
law stream_failure_entry_answers:
  for +q: FSf.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FSf.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW stream_failure_entry_reads (R5): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law stream_failure_entry_reads:
  for +q: FSf.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FSf.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSf.Req>}

# LAW stream_failure_entry_exact (R5): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question,
#   cause or block, a malformed field, input left over)
law stream_failure_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSf.ffi(s)) == False{} : Bool}
  exs r: FSf.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW stream_failure_entry_refuses (R5): every error the entry answers is
# exactly `E stream_failure: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law stream_failure_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSf.ffi(s)) == True{} : Bool}
  {FSf.ffi(s) == Wr.err("stream_failure: malformed request") : String}

# LAW stream_failure_entry_example (R5): anchor: the wire strings Rust
# sends and the replies it reads; an unknown question, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law stream_failure_entry_example:
  {[FSf.ffi("0,1,16,overloaded_error0,"), FSf.ffi("6,3,abc"), FSf.ffi("7,3,1,3,\"a\""), FSf.ffi("8,"), FSf.ffi("6,3,abcx")] == ["3,", "3,abc", "62,Provider stream repeating: the same line 3 times in a row: \"a\"1,", Wr.err("stream_failure: malformed request"), Wr.err("stream_failure: malformed request")] : List<&2, String>}
