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

# R1: the table of causes, in R1's order: each rule's cause, the exact
# lowered type it takes (refusal), the needles found in the lowered type
# (TextPat.sp_any, the laws' matcher), the statuses it takes and the least
# status of a range it takes (500 and more). The data is R1's text; the
# Rust tests of crates/eukhe-bend/src/rules/stream_failure.rs pin rows of it.
type SfRule is Data:
  SfRule{cause: Sf.Cause, word: Maybe<&2, String>, pats: List<&2, Tp.Pat>, sts: List<&2, Nat>, from: Maybe<&2, Nat>}

# R1: content.?filter and access.?denied, with their literal neighbours
def sp_safety() -> Tp.Pat:
  Tp.Pat{False{}, [OverflowLaws.sp_s("sensitive", []), OverflowLaws.sp_s("safety", []), OverflowLaws.sp_s("prohibited_content", []), OverflowLaws.sp_s("blocklist", []), OverflowLaws.sp_s("spii", []), OverflowLaws.sp_s("recitation", []), OverflowLaws.sp_s("contentfilter", []), OverflowLaws.sp_s("content", Tp.One{Tp.CAny{}} <> OverflowLaws.sp_s("filter", [])), OverflowLaws.sp_s("guardrail", []), OverflowLaws.sp_s("flagged", [])]}

def sp_permission() -> Tp.Pat:
  Tp.Pat{False{}, [OverflowLaws.sp_s("permission", []), OverflowLaws.sp_s("forbidden", []), OverflowLaws.sp_s("accessdenied", []), OverflowLaws.sp_s("access", Tp.One{Tp.CAny{}} <> OverflowLaws.sp_s("denied", []))]}

# R1: needles of plain text, found anywhere
def sf_needles(xs: List<&2, String>) -> List<&2, Tp.Pat>:
  [Tp.Pat{False{}, OverflowLaws.sp_lits(xs)}]

def sf_r_payment() -> SfRule:
  SfRule{Sf.KPayment{}, None{}, [], [402n], None{}}

def sf_r_refusal() -> SfRule:
  SfRule{Sf.KRefusal{}, Some{"refusal"}, [], [], None{}}

def sf_r_safety() -> SfRule:
  SfRule{Sf.KSafety{}, None{}, [sp_safety()], [], None{}}

def sf_r_overloaded() -> SfRule:
  SfRule{Sf.KOverloaded{}, None{}, sf_needles(["overloaded"]), [529n], None{}}

def sf_r_rate() -> SfRule:
  SfRule{Sf.KRateLimit{}, None{}, sf_needles(["rate_limit", "usage_limit", "usage_not_included", "throttl"]), [429n], None{}}

def sf_r_auth() -> SfRule:
  SfRule{Sf.KAuth{}, None{}, sf_needles(["authentication", "unauthorized"]), [401n], None{}}

def sf_r_permission() -> SfRule:
  SfRule{Sf.KPermission{}, None{}, [sp_permission()], [403n], None{}}

def sf_r_invalid() -> SfRule:
  SfRule{Sf.KInvalid{}, None{}, sf_needles(["invalid_request", "not_found_error"]), [400n, 404n], None{}}

def sf_r_malformed() -> SfRule:
  SfRule{Sf.KMalformed{}, None{}, sf_needles(["malformed"]), [], None{}}

def sf_r_server() -> SfRule:
  SfRule{Sf.KServer{}, None{}, sf_needles(["api_error", "server_error", "unavailable"]), [], Some{500n}}

# R1: the rules, first to last
def sf_rules() -> List<&2, SfRule>:
  [sf_r_payment(), sf_r_refusal(), sf_r_safety(), sf_r_overloaded(), sf_r_rate(), sf_r_auth(), sf_r_permission(), sf_r_invalid(), sf_r_malformed(), sf_r_server()]

def sf_cause(r: SfRule) -> Sf.Cause:
  match r:
    case SfRule{k, w, ps, sts, from}:
      k

def sf_word(w: Maybe<&2, String>, +t: String) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{x}:
      String.eq(t, x)

# the status s is one of sts, or at least from
def sf_code(+s: Nat, sts: List<&2, Nat>, from: Maybe<&2, Nat>) -> Bool:
  match sts:
    case Nil{}:
      match from:
        case None{}:
          False{}
        case Some{m}:
          Nat.is_le(m, s)
    case n <> rest:
      Bool.or(Nat.is_eq(s, n), sf_code(s, rest, from))

def sf_status(st: Maybe<&2, Nat>, sts: List<&2, Nat>, from: Maybe<&2, Nat>) -> Bool:
  match st:
    case None{}:
      False{}
    case Some{s}:
      sf_code(s, sts, from)

# rule r holds of the lowered type t and the status st
def sf_fires(r: SfRule, +t: String, st: Maybe<&2, Nat>) -> Bool:
  match r:
    case SfRule{k, w, ps, sts, from}:
      Bool.or(sf_word(w, t), Bool.or(TextPat.sp_any(t, ps), sf_status(st, sts, from)))

# no rule of rs holds
def sf_none_fire(rs: List<&2, SfRule>, +t: String, +st: Maybe<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(Bool.not(sf_fires(r, t, st)), sf_none_fire(rest, t, st))

# R1: the text searched: the type lowered (laws/text_pat.bend sp_lower), the
# empty text without one
def sf_lowered(t: Maybe<&2, String>) -> String:
  match t:
    case None{}:
      ""
    case Some{x}:
      TextPat.sp_lower(x)

# R2: the texts of the causes (the table of R2; the Rust test
# the_tag_tables_name_what_the_core_names lists the same texts)
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

# R3: a when there is one, else b
def sp_or(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

# R3: an auth or permission cause (one only a structured type may give)
def sf_auth_like(k: Sf.Cause) -> Bool:
  match k:
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
      True{}
    case Sf.KPermission{}:
      True{}
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

# R3: the unknown cause
def sf_is_unknown(k: Sf.Cause) -> Bool:
  match k:
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
    case Sf.KUnknown{}:
      True{}

def sf_msg_pick(u: Bool, k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match u:
    case True{}:
      None{}
    case False{}:
      Some{Sf.message(k, t, st, d, r)}

# R3: the user's message of an HTTP error of cause k: none for an unknown
# cause (the raw message stays), else the R2 message
def sf_msg_of(+k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  sf_msg_pick(sf_is_unknown(k), k, t, st, d, r)

# the parts of an HTTP error's answer
def sf_kind(h: Sf.Http) -> Sf.Cause:
  match h:
    case Sf.Http{k, t, m}:
      k

def sf_ptype(h: Sf.Http) -> Maybe<&2, String>:
  match h:
    case Sf.Http{k, t, m}:
      t

def sf_msg(h: Sf.Http) -> Maybe<&2, String>:
  match h:
    case Sf.Http{k, t, m}:
      m

# the parts of a named failure
def sf_nkind(n: Sf.Named) -> Sf.Cause:
  match n:
    case Sf.Named{k, m}:
      k

def sf_nmsg(n: Sf.Named) -> String:
  match n:
    case Sf.Named{k, m}:
      m

def sp_shown.pick(short: Bool, +s: String) -> String:
  match short:
    case True{}:
      s
    case False{}:
      String.append(String.take(s, 80n), SCon{Chr{8230}, SNil{}})

# R4: a repeated line as a message shows it
def sp_shown(+s: String) -> String:
  sp_shown.pick(Nat.is_le(String.length(s), 80n), s)


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

# the reply to a request: the decision of the code, which the laws above
# pin, spelled
def sp_w_reply(q: FSf.Req) -> String:
  match q:
    case FSf.QClassify{t, st}:
      sp_w_cause(Sf.classify(t, st), "")
    case FSf.QMessage{k, t, st, d, r}:
      Wr.put_str(Sf.message(k, t, st, d, r), "")
    case FSf.QHttp{m, st, bt, d, code, sdk, r}:
      sp_w_http(Sf.http(m, st, bt, d, code, sdk, r))
    case FSf.QFromStop{raw, r}:
      sp_w_named(Sf.from_stop(raw, r))
    case FSf.QDrop{b}:
      Wr.put_str(Sf.drop(b), "")
    case FSf.QStalled{ms}:
      Wr.put_str(Sf.stalled(ms), "")
    case FSf.QShown{line}:
      Wr.put_str(Sf.shown(line), "")
    case FSf.QRepeating{limit, period, q}:
      sp_w_repeat(Sf.repeating(limit, period, q))

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

# Laws: the causes (R1)
# ---------------------

# LAW stream_failure_classify_first (R1): the cause of a provider error type
# (or none) and a status is the cause of the first rule of R1's table that
# holds of the lowered type (sf_lowered) and the status: a rule that holds
# with none before it holding gives its cause
# EXCLUDES: a rule out of order (a 402 read after the type, a rate limit
#   before the overload), a needle dropped or added, a type searched
#   without lowering, `.?` that takes two chars or a line feed, a status
#   compared wrongly, a refusal found inside a longer type
law stream_failure_classify_first:
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  for +pre: List<&2, SfRule>
  for +x: SfRule
  for +post: List<&2, SfRule>
  for hr: {sf_rules() == List.append(&2, SfRule, pre, x <> post) : List<&2, SfRule>}
  for hx: {sf_fires(x, sf_lowered(t), st) == True{} : Bool}
  for hp: {sf_none_fire(pre, sf_lowered(t), st) == True{} : Bool}
  {Sf.classify(t, st) == sf_cause(x) : Sf.Cause}

# LAW stream_failure_classify_none (R1): when no rule of R1's table holds
# of the lowered type and the status, the cause is unknown
# EXCLUDES: a default cause other than unknown, a cause read from a needle
#   or status no rule names
law stream_failure_classify_none:
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  for hp: {sf_none_fire(sf_rules(), sf_lowered(t), st) == True{} : Bool}
  {Sf.classify(t, st) == Sf.KUnknown{} : Sf.Cause}

# Laws: the messages (R2)
# -----------------------

# LAW stream_failure_message_text (R2): the message of a cause with no
# type, status, detail or request id is the cause's text (R2's table)
# EXCLUDES: a cause's text changed or swapped with another's
law stream_failure_message_text:
  for +k: Sf.Cause
  {Sf.message(k, None{}, None{}, None{}, None{}) == sp_text(k) : String}

# LAW stream_failure_message_quals (R2): with a provider error type x and no
# status, the cause's text is followed by " (x)"; with a status s and no
# type, by " (s)"; with both, by " (x, s)"
# EXCLUDES: a qualifier dropped, swapped or doubled, another separator or
#   bracket, the status before the type
law stream_failure_message_quals:
  for +k: Sf.Cause
  for +x: String
  for +s: Nat
  {Sf.message(k, Some{x}, None{}, None{}, None{}) == String.concat([sp_text(k), " (", x, ")"]) : String} & {Sf.message(k, None{}, Some{s}, None{}, None{}) == String.concat([sp_text(k), " (", Nat.show(s), ")"]) : String} & {Sf.message(k, Some{x}, Some{s}, None{}, None{}) == String.concat([sp_text(k), " (", x, ", ", Nat.show(s), ")"]) : String}

# LAW stream_failure_message_detail (R2): a detail d follows the message
# without it, after ": ", for every cause, type and status
# EXCLUDES: the detail dropped, put before the qualifiers, or joined by
#   another separator
law stream_failure_message_detail:
  for +k: Sf.Cause
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  for +d: String
  {Sf.message(k, t, st, Some{d}, None{}) == String.append(Sf.message(k, t, st, None{}, None{}), String.append(": ", d)) : String}

# LAW stream_failure_message_request_id (R2): a request id r follows the
# message without it as " [request_id: r]", for every cause, type, status
# and detail
# EXCLUDES: the request id dropped, put before the detail, or bracketed
#   another way
law stream_failure_message_request_id:
  for +k: Sf.Cause
  for +t: Maybe<&2, String>
  for +st: Maybe<&2, Nat>
  for +d: Maybe<&2, String>
  for +r: String
  {Sf.message(k, t, st, d, Some{r}) == String.append(Sf.message(k, t, st, d, None{}), String.concat([" [request_id: ", r, "]"])) : String}

# Laws: HTTP errors (R3)
# ----------------------

# LAW stream_failure_http_type (R3): an HTTP error's provider error type is
# the body's error type, else the error's own code, else its SDK class name
# EXCLUDES: another precedence of the three, a type made up from the
#   message
law stream_failure_http_type:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +bt: Maybe<&2, String>
  for +d: Maybe<&2, String>
  for +code: Maybe<&2, String>
  for +sdk: Maybe<&2, String>
  for +r: Maybe<&2, String>
  {sf_ptype(Sf.http(m, st, bt, d, code, sdk, r)) == sp_or(bt, sp_or(code, sdk)) : Maybe<&2, String>}

# LAW stream_failure_http_typed (R3): with a provider error type y, the
# cause is R1's for y and the status, whatever the message
# EXCLUDES: the message searched when a type exists, a type's auth cause
#   replaced by the status's
law stream_failure_http_typed:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +bt: Maybe<&2, String>
  for +d: Maybe<&2, String>
  for +code: Maybe<&2, String>
  for +sdk: Maybe<&2, String>
  for +r: Maybe<&2, String>
  for +y: String
  for hy: {sp_or(bt, sp_or(code, sdk)) == Some{y} : Maybe<&2, String>}
  {sf_kind(Sf.http(m, st, bt, d, code, sdk, r)) == Sf.classify(Some{y}, st) : Sf.Cause}

# LAW stream_failure_http_typeless_kept (R3): with no provider error type,
# the cause is R1's for the message and the status when that is no auth or
# permission cause
# EXCLUDES: a cause from the message dropped for the status's, the message
#   not searched without a type
law stream_failure_http_typeless_kept:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +d: Maybe<&2, String>
  for +r: Maybe<&2, String>
  for hk: {sf_auth_like(Sf.classify(Some{m}, st)) == False{} : Bool}
  {sf_kind(Sf.http(m, st, None{}, d, None{}, None{}, r)) == Sf.classify(Some{m}, st) : Sf.Cause}

# LAW stream_failure_http_typeless_status (R3): with no provider error type,
# an auth or permission cause read from the message gives way to R1's
# cause for the status alone
# EXCLUDES: an auth failure read from words of a message (no structured
#   type), so a retry ladder stops on a transient error
law stream_failure_http_typeless_status:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +d: Maybe<&2, String>
  for +r: Maybe<&2, String>
  for hk: {sf_auth_like(Sf.classify(Some{m}, st)) == True{} : Bool}
  {sf_kind(Sf.http(m, st, None{}, d, None{}, None{}, r)) == Sf.classify(None{}, st) : Sf.Cause}

# LAW stream_failure_http_message (R3): an HTTP error's user message is none
# for an unknown cause (the raw message stays) and else the R2 message of
# its cause, its provider error type, the status, the body's message as
# detail and the request id
# EXCLUDES: a message for an unknown cause, the body's message or the
#   request id dropped, a type other than the provider error type named
law stream_failure_http_message:
  for +m: String
  for +st: Maybe<&2, Nat>
  for +bt: Maybe<&2, String>
  for +d: Maybe<&2, String>
  for +code: Maybe<&2, String>
  for +sdk: Maybe<&2, String>
  for +r: Maybe<&2, String>
  {sf_msg(Sf.http(m, st, bt, d, code, sdk, r)) == sf_msg_of(sf_kind(Sf.http(m, st, bt, d, code, sdk, r)), sf_ptype(Sf.http(m, st, bt, d, code, sdk, r)), st, d, r) : Maybe<&2, String>}

# Laws: stream ends (R4)
# ----------------------

# LAW stream_failure_from_stop_kind (R4): a stream that ended with an error
# stop reason x has R1's cause of x with no status; one with no reason is
# unknown
# EXCLUDES: a reason classified with a status, a missing reason given a
#   cause
law stream_failure_from_stop_kind:
  for +x: String
  for +r: Maybe<&2, String>
  {sf_nkind(Sf.from_stop(Some{x}, r)) == Sf.classify(Some{x}, None{}) : Sf.Cause} & {sf_nkind(Sf.from_stop(None{}, r)) == Sf.KUnknown{} : Sf.Cause}

# LAW stream_failure_from_stop_message (R4): with no request id, a stop
# reason x reads as its cause's text then " (x)", and no reason as
# "Provider stream failed: stream ended with an error and no stop reason"
# EXCLUDES: a message without the reason, another text for a missing
#   reason, a status qualifier made up
law stream_failure_from_stop_message:
  for +x: String
  {sf_nmsg(Sf.from_stop(Some{x}, None{})) == String.concat([sp_text(Sf.classify(Some{x}, None{})), " (", x, ")"]) : String} & {sf_nmsg(Sf.from_stop(None{}, None{})) == "Provider stream failed: stream ended with an error and no stop reason" : String}

# LAW stream_failure_from_stop_request_id (R4, R2): a request id r follows
# a stopped stream's message as " [request_id: r]", with a reason or none
# EXCLUDES: the request id dropped from a stopped stream's message
law stream_failure_from_stop_request_id:
  for +raw: Maybe<&2, String>
  for +r: String
  {sf_nmsg(Sf.from_stop(raw, Some{r})) == String.append(sf_nmsg(Sf.from_stop(raw, None{})), String.concat([" [request_id: ", r, "]"])) : String}

# LAW stream_failure_stalled (R4): a stalled stream reads "Provider stream
# stalled: no stream event for <ms>ms", ms as the host writes it
# EXCLUDES: a stall without its deadline, another unit or text
law stream_failure_stalled:
  for +ms: String
  {Sf.stalled(ms) == String.concat(["Provider stream stalled: no stream event for ", ms, "ms"]) : String}

# LAW stream_failure_shown (R4): every repeated line shows as the spec
# says: its first 80 chars and U+2026 when longer, else whole
# EXCLUDES: a cut at 79 or 81 chars, a cut line without the mark, a mark
#   on a line of exactly 80 chars
law stream_failure_shown:
  for +s: String
  {Sf.shown(s) == sp_shown(s) : String}

# LAW stream_failure_repeating_line (R4): a repeating stream of period 0 or
# 1 reads "Provider stream repeating: the same line <limit> times in a row:
# <q>" and records the period 1
# EXCLUDES: a cycle of one line read as a cycle, a period of 0 recorded,
#   the limit dropped
law stream_failure_repeating_line:
  for +limit: Nat
  for +period: Nat
  for +q: String
  for h: {Nat.is_le(period, 1n) == True{} : Bool}
  {Sf.repeating(limit, period, q) == Sf.Repeat{String.concat(["Provider stream repeating: the same line ", Nat.show(limit), " times in a row: ", q]), 1n} : Sf.Repeat}

# LAW stream_failure_repeating_cycle (R4): a repeating stream of period p
# of 2 or more reads "Provider stream repeating: a cycle of <p> lines
# repeated over the last <limit> lines, ending with <q>" and records p
# EXCLUDES: the limit and the period swapped in the text, another period
#   recorded
law stream_failure_repeating_cycle:
  for +limit: Nat
  for +period: Nat
  for +q: String
  for h: {Nat.is_le(2n, period) == True{} : Bool}
  {Sf.repeating(limit, period, q) == Sf.Repeat{String.concat(["Provider stream repeating: a cycle of ", Nat.show(period), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]), period} : Sf.Repeat}

# LAW stream_failure_example (R1-R4): anchor: the vectors of the Rust
# tests: classification by type and status (a 402 before the type), the
# messages with and without qualifiers, the stop reasons
# EXCLUDES: a classification or message that drifts from the Rust test
#   vectors
law stream_failure_example:
  {([Sf.classify(Some{"refusal"}, None{}), Sf.classify(Some{"SAFETY"}, None{}), Sf.classify(Some{"overloaded_error"}, None{}), Sf.classify(Some{"other"}, Some{529n}), Sf.classify(Some{"rate_limit_error"}, None{}), Sf.classify(Some{"usage_not_included"}, None{}), Sf.classify(Some{"authentication_error"}, None{}), Sf.classify(Some{"forbidden"}, None{}), Sf.classify(Some{"invalid_request_error"}, None{}), Sf.classify(Some{"api_error"}, None{}), Sf.classify(Some{"other"}, Some{503n}), Sf.classify(Some{"weird"}, None{}), Sf.classify(Some{"invalid_request_error"}, Some{402n}), Sf.classify(None{}, Some{402n}), Sf.classify(Some{"Content-Filter"}, None{})], ([Sf.message(Sf.KOverloaded{}, Some{"overloaded_error"}, Some{529n}, Some{"slow down"}, Some{"req_abc"}), Sf.message(Sf.KInvalid{}, None{}, Some{400n}, None{}, None{})], [Sf.from_stop(Some{"refusal"}, None{}), Sf.from_stop(None{}, None{})])) == ([Sf.KRefusal{}, Sf.KSafety{}, Sf.KOverloaded{}, Sf.KOverloaded{}, Sf.KRateLimit{}, Sf.KRateLimit{}, Sf.KAuth{}, Sf.KPermission{}, Sf.KInvalid{}, Sf.KServer{}, Sf.KServer{}, Sf.KUnknown{}, Sf.KPayment{}, Sf.KPayment{}, Sf.KSafety{}], (["Provider overloaded (overloaded_error, 529): slow down [request_id: req_abc]", "Provider rejected the request (400)"], [Sf.Named{Sf.KRefusal{}, "Model refused to respond (refusal)"}, Sf.Named{Sf.KUnknown{}, "Provider stream failed: stream ended with an error and no stop reason"}])) : List<&2, Sf.Cause> & (List<&2, String> & List<&2, Sf.Named>)}

# LAW stream_failure_http_example (R3): anchor: a body type, an SDK class
# name standing in for the type, an auth word in a message without a type
# (the status decides), an unknown cause keeping the raw message
# EXCLUDES: a precedence or fallback that drifts from the Rust
law stream_failure_http_example:
  {[Sf.http("429 x", Some{429n}, None{}, Some{"slow"}, None{}, Some{"ApiError"}, None{}), Sf.http("unauthorized here", Some{400n}, None{}, None{}, None{}, None{}, Some{"r1"}), Sf.http("odd", None{}, None{}, None{}, None{}, None{}, None{}), Sf.http("x", Some{500n}, Some{"overloaded_error"}, Some{"busy"}, Some{"c"}, None{}, None{})] == [Sf.Http{Sf.KRateLimit{}, Some{"ApiError"}, Some{"Provider rate limit exceeded (ApiError, 429): slow"}}, Sf.Http{Sf.KInvalid{}, None{}, Some{"Provider rejected the request (400) [request_id: r1]"}}, Sf.Http{Sf.KUnknown{}, None{}, None{}}, Sf.Http{Sf.KOverloaded{}, Some{"overloaded_error"}, Some{"Provider overloaded (overloaded_error, 500): busy"}}] : List<&2, Sf.Http>}

# LAW stream_failure_drop_example (R4): anchor: the message of a stream
# dropped inside each block, as the Rust test
# the_tag_tables_name_what_the_core_names reads it (crates/eukhe-bend/src/
# rules/stream_failure.rs), every block
# EXCLUDES: another detail per block, a drop without its type
law stream_failure_drop_example:
  {[Sf.drop(Sf.BThinking{}), Sf.drop(Sf.BText{}), Sf.drop(Sf.BToolCall{}), Sf.drop(Sf.BNone{})] == ["Provider dropped the response stream (stream_drop): the stream ended inside a thinking block before the stop signal", "Provider dropped the response stream (stream_drop): the stream ended inside a text block before the stop signal", "Provider dropped the response stream (stream_drop): the stream ended inside a tool-call block before the stop signal", "Provider dropped the response stream (stream_drop): the stream ended before any response content or stop signal"] : List<&2, String>}

# Laws: the entry (R5)
# --------------------

# LAW stream_failure_entry_answers (R5): the entry answers every request
# Rust spells, every number and length within the wire, with the spelled
# answer of the rules (bend/stream_failure.bend, pinned by the laws above)
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
