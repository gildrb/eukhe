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
# laws/text_pat.bend (text_pat_fold).
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

# the chars of s as items, before rest
def sp_s(s: String, rest: List<&2, P.It>) -> List<&2, P.It>:
  match s:
    case SNil{}:
      rest
    case SCon{+c, t}:
      P.One{P.CIn{Char.to_u32(c), Char.to_u32(c)}} <> sp_s(t, rest)

# R1: gap, jsgap, digits
def sp_gap() -> P.It:
  P.Opt{P.COut{['\n']}}

def sp_jsgap() -> P.It:
  P.Opt{P.COut{['\n', '\r', Chr{8232}, Chr{8233}]}}

def sp_digits(rest: List<&2, P.It>) -> List<&2, P.It>:
  P.One{P.CIn{48, 57}} <> P.Star{P.CIn{48, 57}} <> rest

# a, then the item g, then b
def sp_two(a: String, g: P.It, b: String) -> List<&2, P.It>:
  sp_s(a, g <> sp_s(b, []))

# R1: each text found anywhere
def sp_anys(xs: List<&2, String>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{P.EFree{}, sp_s(x, []), P.EFree{}} <> sp_anys(t)

# R1: each list of items found as a whole word
def sp_wholes(xs: List<&2, List<&2, P.It>>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{P.EWord{}, x, P.EWord{}} <> sp_wholes(t)

# R1: each text found as a whole word
def sp_words(xs: List<&2, String>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{P.EWord{}, sp_s(x, []), P.EWord{}} <> sp_words(t)

# R1: each list of items found starting a word
def sp_starts(xs: List<&2, List<&2, P.It>>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{P.EWord{}, x, P.EFree{}} <> sp_starts(t)

# R2: (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing
def sp_terminal() -> List<&2, P.Ph>:
  sp_anys(["gousagelimiterror", "freeusagelimiterror", "monthly usage limit reached", "available balance", "insufficient_quota", "out of budget", "quota exceeded", "billing"])

# R2: (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing|subscription_sharing_usage_limit_exceeded|provider admission queue is full|server requested \d+s retry delay
def sp_limit() -> List<&2, P.Ph>:
  List.concat(&2, P.Ph, [sp_terminal(), sp_anys(["subscription_sharing_usage_limit_exceeded", "provider admission queue is full"]), [P.Ph{P.EFree{}, sp_s("server requested ", sp_digits(sp_s("s retry delay", []))), P.EFree{}}]])

# R2: (?i)\boverloaded|\bserver_busy\b|servers are currently busy|currently experiencing high demand|model is at capacity|\brate.?limit|\btoo many requests\b|\b(?:408|429|500|502|503|504|520|524|529)\b|\bservice.?unavailable\b|\bserver.?error\b|\binternal.?error\b|\bprovider.?returned.?error\b|exceeded request buffer limit while retrying upstream|\bnetwork.?error\b|\bconnection.?error\b|\bconnection.?refused\b|\bconnection.?lost\b|other side closed|\bfetch failed\b|\bgetaddrinfo\b|\bENOTFOUND\b|\bEAI_AGAIN\b|\bupstream.?connect|reset before headers|\bsocket hang up\b|socket connection was closed|\btimed? ?out\b|\bterminated\b|\bwebsocket.?closed\b|\bwebsocket.?error\b|\bended without\b|stream ended before message_stop|stream ended before a terminal response event|http2 request did not get a response|pending stream has been canceled|you can retry your request|try your request again|please retry your request|\bResourceExhausted\b|\bsubscription_sharing_usage_unavailable\b|\bsubscription_sharing_user_unavailable\b
def sp_transient() -> List<&2, P.Ph>:
  List.concat(&2, P.Ph, [
    sp_starts([sp_s("overloaded", []), sp_two("rate", sp_gap(), "limit"), sp_two("upstream", sp_gap(), "connect")]),
    sp_wholes([sp_two("service", sp_gap(), "unavailable"), sp_two("server", sp_gap(), "error"), sp_two("internal", sp_gap(), "error"), sp_s("provider", sp_gap() <> sp_s("returned", sp_gap() <> sp_s("error", []))), sp_two("network", sp_gap(), "error"), sp_two("connection", sp_gap(), "error"), sp_two("connection", sp_gap(), "refused"), sp_two("connection", sp_gap(), "lost"), sp_two("websocket", sp_gap(), "closed"), sp_two("websocket", sp_gap(), "error")]),
    sp_words(["server_busy", "too many requests", "408", "429", "500", "502", "503", "504", "520", "524", "529", "fetch failed", "getaddrinfo", "enotfound", "eai_again", "socket hang up", "timed out", "timedout", "time out", "timeout", "terminated", "ended without", "resourceexhausted", "subscription_sharing_usage_unavailable", "subscription_sharing_user_unavailable"]),
    sp_anys(["servers are currently busy", "currently experiencing high demand", "model is at capacity", "exceeded request buffer limit while retrying upstream", "other side closed", "reset before headers", "socket connection was closed", "stream ended before message_stop", "stream ended before a terminal response event", "http2 request did not get a response", "pending stream has been canceled", "you can retry your request", "try your request again", "please retry your request"])
  ])

# R2: (?i)rate[^\n\r\u{2028}\u{2029}]?limit|overloaded|service[^\n\r\u{2028}\u{2029}]?unavailable|upstream[^\n\r\u{2028}\u{2029}]?connect|connection[^\n\r\u{2028}\u{2029}]?refused
def sp_codex_retryable() -> List<&2, P.Ph>:
  [P.Ph{P.EFree{}, sp_two("rate", sp_jsgap(), "limit"), P.EFree{}}, P.Ph{P.EFree{}, sp_s("overloaded", []), P.EFree{}}, P.Ph{P.EFree{}, sp_two("service", sp_jsgap(), "unavailable"), P.EFree{}}, P.Ph{P.EFree{}, sp_two("upstream", sp_jsgap(), "connect"), P.EFree{}}, P.Ph{P.EFree{}, sp_two("connection", sp_jsgap(), "refused"), P.EFree{}}]

# R2: (?i)usage_limit_reached|usage_not_included|rate_limit_exceeded
def sp_codex_usage() -> List<&2, P.Ph>:
  sp_anys(["usage_limit_reached", "usage_not_included", "rate_limit_exceeded"])

# R2: (?i)timed? ?out
def sp_timeout() -> List<&2, P.Ph>:
  sp_anys(["timed out", "timedout", "time out", "timeout"])

# R2: the table of each rule
def sp_table(r: E.Rule) -> List<&2, P.Ph>:
  match r:
    case E.RLimit{}:
      sp_limit()
    case E.RTransient{}:
      sp_transient()
    case E.RCodexTerminal{}:
      sp_terminal()
    case E.RCodexRetryable{}:
      sp_codex_retryable()
    case E.RCodexUsage{}:
      sp_codex_usage()
    case E.RTimeout{}:
      sp_timeout()

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

# LAW err_text_decides (R1, R2): whether every rule holds for every list
# of texts is the spec's
# EXCLUDES: a phrase dropped, changed or moved to another table, an edge
#   changed (a whole word searched anywhere, a word start asked of the
#   end), gap and jsgap swapped, a case-sensitive search, a text of the
#   list skipped, an empty list read as a hit
law err_text_decides:
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
