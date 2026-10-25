# err_text: whether an error text from a provider reads as one of six
# kinds (Rust: the `regex` patterns of eukhe-ai utils/retry.rs,
# api/openai_codex_responses/errors.rs and api/anthropic_messages/client.rs;
# laws/err_text.bend). Each kind is a table of explicit phrases
# (bend/phrase.bend), all lowercase, searched in the folded text
# (bend/text_pat.bend `fold_str`: what a case-insensitive regex `(?i)` sees
# for a lowercase ASCII pattern). Above each table: the regex it replaced.
# Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as Tp
import ./phrase.bend as P

# The kinds of error text
type Rule is Data:
  # a provider limit no retry helps (retry.rs)
  RLimit{}
  # a transient provider error worth a retry (retry.rs)
  RTransient{}
  # the Codex client's terminal rate limit (errors.rs)
  RCodexTerminal{}
  # the Codex client's retryable text (errors.rs)
  RCodexRetryable{}
  # the Codex client's usage-limit codes (errors.rs)
  RCodexUsage{}
  # a timeout (client.rs)
  RTimeout{}

# Items
# -----

# optionally one char that is no line feed (regex `.?`)
def gap() -> P.It:
  P.Opt{P.COut{['\n']}}

# optionally one char that is no line terminator (the JS `.?` of the Codex
# client: no line feed, carriage return, U+2028 or U+2029)
def jsgap() -> P.It:
  P.Opt{P.COut{['\n', '\r', Chr{8232}, Chr{8233}]}}

# one or more ASCII digits (regex `\d+`), before rest
def digits(rest: List<&2, P.It>) -> List<&2, P.It>:
  +d = {P.CIn{48, 57} : P.Cls}
  P.One{d} <> P.Star{d} <> rest

# a then the item g then b
def gapped(a: String, g: P.It, b: String) -> List<&2, P.It>:
  P.lit(a, g <> P.lit(b, []))

# each text of xs found anywhere, before rest
def anywheres(xs: List<&2, String>, rest: List<&2, P.Ph>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      P.anywhere(P.lit(x, [])) <> anywheres(t, rest)

# each text of xs found as a whole word, before rest
def words(xs: List<&2, String>, rest: List<&2, P.Ph>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      P.word(P.lit(x, [])) <> words(t, rest)

# Tables
# ------

# (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing
# (errors.rs TERMINAL_RATE_LIMIT; also the head of retry.rs's limit
# regex), before rest
def terminal_phs(rest: List<&2, P.Ph>) -> List<&2, P.Ph>:
  anywheres(["gousagelimiterror", "freeusagelimiterror", "monthly usage limit reached", "available balance", "insufficient_quota", "out of budget", "quota exceeded", "billing"], rest)

# (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing|subscription_sharing_usage_limit_exceeded|provider admission queue is full|server requested \d+s retry delay
# (retry.rs NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN)
def limit_phs() -> List<&2, P.Ph>:
  terminal_phs(anywheres(["subscription_sharing_usage_limit_exceeded", "provider admission queue is full"], [P.anywhere(P.lit("server requested ", digits(P.lit("s retry delay", []))))]))

# (?i)\boverloaded|\bserver_busy\b|servers are currently busy|currently experiencing high demand|model is at capacity|\brate.?limit|\btoo many requests\b|\b(?:408|429|500|502|503|504|520|524|529)\b|\bservice.?unavailable\b|\bserver.?error\b|\binternal.?error\b|\bprovider.?returned.?error\b|exceeded request buffer limit while retrying upstream|\bnetwork.?error\b|\bconnection.?error\b|\bconnection.?refused\b|\bconnection.?lost\b|other side closed|\bfetch failed\b|\bgetaddrinfo\b|\bENOTFOUND\b|\bEAI_AGAIN\b|\bupstream.?connect|reset before headers|\bsocket hang up\b|socket connection was closed|\btimed? ?out\b|\bterminated\b|\bwebsocket.?closed\b|\bwebsocket.?error\b|\bended without\b|stream ended before message_stop|stream ended before a terminal response event|http2 request did not get a response|pending stream has been canceled|you can retry your request|try your request again|please retry your request|\bResourceExhausted\b|\bsubscription_sharing_usage_unavailable\b|\bsubscription_sharing_user_unavailable\b
# (retry.rs RETRYABLE_PROVIDER_ERROR_PATTERN)
def transient_phs() -> List<&2, P.Ph>:
  +g = gap()
  P.word_start(P.lit("overloaded", [])) <> P.word_start(gapped("rate", g, "limit")) <> P.word_start(gapped("upstream", g, "connect")) <> P.word(gapped("service", g, "unavailable")) <> P.word(gapped("server", g, "error")) <> P.word(gapped("internal", g, "error")) <> P.word(P.lit("provider", g <> P.lit("returned", g <> P.lit("error", [])))) <> P.word(gapped("network", g, "error")) <> P.word(gapped("connection", g, "error")) <> P.word(gapped("connection", g, "refused")) <> P.word(gapped("connection", g, "lost")) <> P.word(gapped("websocket", g, "closed")) <> P.word(gapped("websocket", g, "error")) <> words(["server_busy", "too many requests", "408", "429", "500", "502", "503", "504", "520", "524", "529", "fetch failed", "getaddrinfo", "enotfound", "eai_again", "socket hang up", "timed out", "timedout", "time out", "timeout", "terminated", "ended without", "resourceexhausted", "subscription_sharing_usage_unavailable", "subscription_sharing_user_unavailable"], anywheres(["servers are currently busy", "currently experiencing high demand", "model is at capacity", "exceeded request buffer limit while retrying upstream", "other side closed", "reset before headers", "socket connection was closed", "stream ended before message_stop", "stream ended before a terminal response event", "http2 request did not get a response", "pending stream has been canceled", "you can retry your request", "try your request again", "please retry your request"], []))

# (?i)rate[^\n\r\u{2028}\u{2029}]?limit|overloaded|service[^\n\r\u{2028}\u{2029}]?unavailable|upstream[^\n\r\u{2028}\u{2029}]?connect|connection[^\n\r\u{2028}\u{2029}]?refused
# (errors.rs RETRYABLE_TEXT)
def codex_retryable_phs() -> List<&2, P.Ph>:
  +g = jsgap()
  [P.anywhere(gapped("rate", g, "limit")), P.anywhere(P.lit("overloaded", [])), P.anywhere(gapped("service", g, "unavailable")), P.anywhere(gapped("upstream", g, "connect")), P.anywhere(gapped("connection", g, "refused"))]

# (?i)usage_limit_reached|usage_not_included|rate_limit_exceeded
# (errors.rs USAGE_LIMIT_CODE)
def codex_usage_phs() -> List<&2, P.Ph>:
  anywheres(["usage_limit_reached", "usage_not_included", "rate_limit_exceeded"], [])

# (?i)timed? ?out
# (client.rs is_timeout_text)
def timeout_phs() -> List<&2, P.Ph>:
  anywheres(["timed out", "timedout", "time out", "timeout"], [])

# the table of a rule
def table(r: Rule) -> List<&2, P.Ph>:
  match r:
    case RLimit{}:
      limit_phs()
    case RTransient{}:
      transient_phs()
    case RCodexTerminal{}:
      terminal_phs([])
    case RCodexRetryable{}:
      codex_retryable_phs()
    case RCodexUsage{}:
      codex_usage_phs()
    case RTimeout{}:
      timeout_phs()

# The decision
# ------------

# whether the rule holds for one text: a phrase of its table is found in
# the folded text
def holds_text(r: Rule, text: String) -> Bool:
  P.any(Tp.fold_str(text), table(r))

# whether the rule holds for one of the texts (lazy: the first hit stops)
def holds(+r: Rule, texts: List<&2, String>) -> Bool:
  match texts:
    case Nil{}:
      False{}
    case t <> more:
      P.pm.or(holds_text(r, t), u => holds(r, more))
