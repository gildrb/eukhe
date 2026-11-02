# err_text: whether an error text from a provider reads as one of six
# kinds (Rust: the `regex` patterns of eukhe-ai utils/retry.rs,
# api/openai_codex_responses/errors.rs and api/anthropic_messages/client.rs;
# laws/err_text.bend). Each kind is a table of explicit phrases
# (bend/phrase.bend), all lowercase, searched in the folded text
# (bend/text_pat.bend `fold_str`: what a case-insensitive regex `(?i)` sees
# for a lowercase ASCII pattern). Above each table: the regex it replaced;
# above each phrase, the phrase as a regex (`.` there: one char that is no
# line terminator of that regex). The tables are written out whole, so the
# compiled core holds them as constants. Pure: no IO, no @unsafe.

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

# Tables
# ------

# (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing
# (errors.rs TERMINAL_RATE_LIMIT; also the head of retry.rs's limit
# regex)
def terminal_phs() -> List<&2, P.Ph>:
  [
    # gousagelimiterror
    P.Ph{P.EFree{}, [P.One{P.CIn{103, 103}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EFree{}},
    # freeusagelimiterror
    P.Ph{P.EFree{}, [P.One{P.CIn{102, 102}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EFree{}},
    # monthly usage limit reached
    P.Ph{P.EFree{}, [P.One{P.CIn{109, 109}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # available balance
    P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}], P.EFree{}},
    # insufficient_quota
    P.Ph{P.EFree{}, [P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{97, 97}}], P.EFree{}},
    # out of budget
    P.Ph{P.EFree{}, [P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # quota exceeded
    P.Ph{P.EFree{}, [P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # billing
    P.Ph{P.EFree{}, [P.One{P.CIn{98, 98}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}], P.EFree{}}
  ]

# (?i)GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached|available balance|insufficient_quota|out of budget|quota exceeded|billing|subscription_sharing_usage_limit_exceeded|provider admission queue is full|server requested \d+s retry delay
# (retry.rs NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN)
def limit_phs() -> List<&2, P.Ph>:
  [
    # gousagelimiterror
    P.Ph{P.EFree{}, [P.One{P.CIn{103, 103}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EFree{}},
    # freeusagelimiterror
    P.Ph{P.EFree{}, [P.One{P.CIn{102, 102}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EFree{}},
    # monthly usage limit reached
    P.Ph{P.EFree{}, [P.One{P.CIn{109, 109}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # available balance
    P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}], P.EFree{}},
    # insufficient_quota
    P.Ph{P.EFree{}, [P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{97, 97}}], P.EFree{}},
    # out of budget
    P.Ph{P.EFree{}, [P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # quota exceeded
    P.Ph{P.EFree{}, [P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # billing
    P.Ph{P.EFree{}, [P.One{P.CIn{98, 98}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}], P.EFree{}},
    # subscription_sharing_usage_limit_exceeded
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # provider admission queue is full
    P.Ph{P.EFree{}, [P.One{P.CIn{112, 112}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{108, 108}}], P.EFree{}},
    # server requested \d+s retry delay
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{48, 57}}, P.Star{P.CIn{48, 57}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{121, 121}}], P.EFree{}}
  ]

# (?i)\boverloaded|\bserver_busy\b|servers are currently busy|currently experiencing high demand|model is at capacity|\brate.?limit|\btoo many requests\b|\b(?:408|429|500|502|503|504|520|524|529)\b|\bservice.?unavailable\b|\bserver.?error\b|\binternal.?error\b|\bprovider.?returned.?error\b|exceeded request buffer limit while retrying upstream|\bnetwork.?error\b|\bconnection.?error\b|\bconnection.?refused\b|\bconnection.?lost\b|other side closed|\bfetch failed\b|\bgetaddrinfo\b|\bENOTFOUND\b|\bEAI_AGAIN\b|\bupstream.?connect|reset before headers|\bsocket hang up\b|socket connection was closed|\btimed? ?out\b|\bterminated\b|\bwebsocket.?closed\b|\bwebsocket.?error\b|\bended without\b|stream ended before message_stop|stream ended before a terminal response event|http2 request did not get a response|pending stream has been canceled|you can retry your request|try your request again|please retry your request|\bResourceExhausted\b|\bsubscription_sharing_usage_unavailable\b|\bsubscription_sharing_user_unavailable\b
# (retry.rs RETRYABLE_PROVIDER_ERROR_PATTERN)
def transient_phs() -> List<&2, P.Ph>:
  [
    # \boverloaded
    P.Ph{P.EWord{}, [P.One{P.CIn{111, 111}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # \brate.?limit
    P.Ph{P.EWord{}, [P.One{P.CIn{114, 114}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # \bupstream.?connect
    P.Ph{P.EWord{}, [P.One{P.CIn{117, 117}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # \bservice.?unavailable\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}], P.EWord{}},
    # \bserver.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \binternal.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{108, 108}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \bprovider.?returned.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{112, 112}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \bnetwork.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{119, 119}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{107, 107}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \bconnection.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \bconnection.?refused\b
    P.Ph{P.EWord{}, [P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \bconnection.?lost\b
    P.Ph{P.EWord{}, [P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \bwebsocket.?closed\b
    P.Ph{P.EWord{}, [P.One{P.CIn{119, 119}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{107, 107}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \bwebsocket.?error\b
    P.Ph{P.EWord{}, [P.One{P.CIn{119, 119}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{107, 107}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.Opt{P.COut{[Chr{10}]}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}], P.EWord{}},
    # \bserver_busy\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{121, 121}}], P.EWord{}},
    # \btoo many requests\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{115, 115}}], P.EWord{}},
    # \b408\b
    P.Ph{P.EWord{}, [P.One{P.CIn{52, 52}}, P.One{P.CIn{48, 48}}, P.One{P.CIn{56, 56}}], P.EWord{}},
    # \b429\b
    P.Ph{P.EWord{}, [P.One{P.CIn{52, 52}}, P.One{P.CIn{50, 50}}, P.One{P.CIn{57, 57}}], P.EWord{}},
    # \b500\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{48, 48}}, P.One{P.CIn{48, 48}}], P.EWord{}},
    # \b502\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{48, 48}}, P.One{P.CIn{50, 50}}], P.EWord{}},
    # \b503\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{48, 48}}, P.One{P.CIn{51, 51}}], P.EWord{}},
    # \b504\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{48, 48}}, P.One{P.CIn{52, 52}}], P.EWord{}},
    # \b520\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{50, 50}}, P.One{P.CIn{48, 48}}], P.EWord{}},
    # \b524\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{50, 50}}, P.One{P.CIn{52, 52}}], P.EWord{}},
    # \b529\b
    P.Ph{P.EWord{}, [P.One{P.CIn{53, 53}}, P.One{P.CIn{50, 50}}, P.One{P.CIn{57, 57}}], P.EWord{}},
    # \bfetch failed\b
    P.Ph{P.EWord{}, [P.One{P.CIn{102, 102}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \bgetaddrinfo\b
    P.Ph{P.EWord{}, [P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{111, 111}}], P.EWord{}},
    # \benotfound\b
    P.Ph{P.EWord{}, [P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \beai_again\b
    P.Ph{P.EWord{}, [P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}], P.EWord{}},
    # \bsocket hang up\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{107, 107}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{112, 112}}], P.EWord{}},
    # \btimed out\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \btimedout\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \btime out\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \btimeout\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \bterminated\b
    P.Ph{P.EWord{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \bended without\b
    P.Ph{P.EWord{}, [P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{119, 119}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EWord{}},
    # \bresourceexhausted\b
    P.Ph{P.EWord{}, [P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EWord{}},
    # \bsubscription_sharing_usage_unavailable\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}], P.EWord{}},
    # \bsubscription_sharing_user_unavailable\b
    P.Ph{P.EWord{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}], P.EWord{}},
    # servers are currently busy
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{121, 121}}], P.EFree{}},
    # currently experiencing high demand
    P.Ph{P.EFree{}, [P.One{P.CIn{99, 99}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # model is at capacity
    P.Ph{P.EFree{}, [P.One{P.CIn{109, 109}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{121, 121}}], P.EFree{}},
    # exceeded request buffer limit while retrying upstream
    P.Ph{P.EFree{}, [P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{119, 119}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}], P.EFree{}},
    # other side closed
    P.Ph{P.EFree{}, [P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # reset before headers
    P.Ph{P.EFree{}, [P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{115, 115}}], P.EFree{}},
    # socket connection was closed
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{107, 107}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{119, 119}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # stream ended before message_stop
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{112, 112}}], P.EFree{}},
    # stream ended before a terminal response event
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # http2 request did not get a response
    P.Ph{P.EFree{}, [P.One{P.CIn{104, 104}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{50, 50}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}], P.EFree{}},
    # pending stream has been canceled
    P.Ph{P.EFree{}, [P.One{P.CIn{112, 112}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # you can retry your request
    P.Ph{P.EFree{}, [P.One{P.CIn{121, 121}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # try your request again
    P.Ph{P.EFree{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}], P.EFree{}},
    # please retry your request
    P.Ph{P.EFree{}, [P.One{P.CIn{112, 112}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{121, 121}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{113, 113}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}], P.EFree{}}
  ]

# (?i)rate[^\n\r\u{2028}\u{2029}]?limit|overloaded|service[^\n\r\u{2028}\u{2029}]?unavailable|upstream[^\n\r\u{2028}\u{2029}]?connect|connection[^\n\r\u{2028}\u{2029}]?refused
# (errors.rs RETRYABLE_TEXT)
def codex_retryable_phs() -> List<&2, P.Ph>:
  [
    # rate.?limit
    P.Ph{P.EFree{}, [P.One{P.CIn{114, 114}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.Opt{P.COut{[Chr{10}, Chr{13}, Chr{8232}, Chr{8233}]}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # overloaded
    P.Ph{P.EFree{}, [P.One{P.CIn{111, 111}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # service.?unavailable
    P.Ph{P.EFree{}, [P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.Opt{P.COut{[Chr{10}, Chr{13}, Chr{8232}, Chr{8233}]}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{118, 118}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{101, 101}}], P.EFree{}},
    # upstream.?connect
    P.Ph{P.EFree{}, [P.One{P.CIn{117, 117}}, P.One{P.CIn{112, 112}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{109, 109}}, P.Opt{P.COut{[Chr{10}, Chr{13}, Chr{8232}, Chr{8233}]}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # connection.?refused
    P.Ph{P.EFree{}, [P.One{P.CIn{99, 99}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{110, 110}}, P.Opt{P.COut{[Chr{10}, Chr{13}, Chr{8232}, Chr{8233}]}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{102, 102}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}}
  ]

# (?i)usage_limit_reached|usage_not_included|rate_limit_exceeded
# (errors.rs USAGE_LIMIT_CODE)
def codex_usage_phs() -> List<&2, P.Ph>:
  [
    # usage_limit_reached
    P.Ph{P.EFree{}, [P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{114, 114}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{104, 104}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # usage_not_included
    P.Ph{P.EFree{}, [P.One{P.CIn{117, 117}}, P.One{P.CIn{115, 115}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{103, 103}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{110, 110}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}},
    # rate_limit_exceeded
    P.Ph{P.EFree{}, [P.One{P.CIn{114, 114}}, P.One{P.CIn{97, 97}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{108, 108}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{116, 116}}, P.One{P.CIn{95, 95}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{120, 120}}, P.One{P.CIn{99, 99}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}], P.EFree{}}
  ]

# (?i)timed? ?out
# (client.rs is_timeout_text)
def timeout_phs() -> List<&2, P.Ph>:
  [
    # timed out
    P.Ph{P.EFree{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # timedout
    P.Ph{P.EFree{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{100, 100}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # time out
    P.Ph{P.EFree{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{32, 32}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EFree{}},
    # timeout
    P.Ph{P.EFree{}, [P.One{P.CIn{116, 116}}, P.One{P.CIn{105, 105}}, P.One{P.CIn{109, 109}}, P.One{P.CIn{101, 101}}, P.One{P.CIn{111, 111}}, P.One{P.CIn{117, 117}}, P.One{P.CIn{116, 116}}], P.EFree{}}
  ]

# the table of a rule
def table(r: Rule) -> List<&2, P.Ph>:
  match r:
    case RLimit{}:
      limit_phs()
    case RTransient{}:
      transient_phs()
    case RCodexTerminal{}:
      terminal_phs()
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
