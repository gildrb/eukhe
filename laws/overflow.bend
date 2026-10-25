# eukhe: the laws of area overflow

import Base
import ../bend/overflow.bend as O
import ../bend/ffi_overflow.bend as FO
import ../bend/text_pat.bend as Tp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./text_pat.bend as TextPat

# (O1) Whether a model reply is a context overflow
# ------------------------------------------------
# bend/overflow.bend, run as the compiled core by bend/ffi_overflow.bend
# (eukhe-bend rules/overflow.rs; asked by eukhe-ai utils/overflow.rs for
# every finished reply). Every input is free: any stop, message, provider,
# window and usage. The search for a pattern is pinned by laws/text_pat.bend
# (text_pat_search_*, text_pat_prefix_*: found exactly where a part of the
# text matches; text_pat_any, text_pat_hit: a table is searched alternative
# by alternative, TextPat.sp_any; text_pat_fold: the case folding).
#
# R1: an error reply is an overflow when its message is not empty, none of
#     the calm patterns is found in it, and an overflow pattern is found in
#     it, or the provider is "cerebras" and the Cerebras pattern is found
#     at its start. The search is case-insensitive: it runs on the folded
#     message (text_pat_fold).
# R2: the patterns, each regex of the Rust it replaced spelled as its
#     alternatives (sp_overflow_pats, sp_cerebras, sp_calm_pats below,
#     one comment per regex).
# R3: with a window (0: none), a stop whose input and cache reads together
#     pass the window is an overflow (z.ai's silent overflow), and so is a
#     length stop with no output whose input and cache reads reach the
#     window minus a hundredth of it rounded down: the least whole count at
#     or above 99% of the window (Xiaomi MiMo; Rust compared the f64
#     `input >= window * 0.99`, the same for every window below 10^13).
#     Nothing else is an overflow.
# R4: a length stop is recoverable when the intended output limit is above
#     0 and the output stayed below it.
# R5: the entry answers each request Rust writes (every number, length and
#     count within the wire) with the answer of R1-R4, reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E overflow: malformed request`.

# Spec helpers
# ------------

# the chars of s as items, before rest
def sp_s(s: String, rest: List<&2, Tp.It>) -> List<&2, Tp.It>:
  match s:
    case SNil{}:
      rest
    case SCon{c, t}:
      Tp.One{Tp.CLit{c}} <> sp_s(t, rest)

# one or more chars of the class, before rest (regex `x+`)
def sp_more(+c: Tp.Cls, rest: List<&2, Tp.It>) -> List<&2, Tp.It>:
  Tp.One{c} <> Tp.Star{c} <> rest

def sp_lits(xs: List<&2, String>) -> List<&2, List<&2, Tp.It>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp_s(x, Nil{}) <> sp_lits(t)

def sp_anywhere(xs: List<&2, String>) -> Tp.Pat:
  Tp.Pat{False{}, sp_lits(xs)}

# R2: `... (?: of [0-9,]+ tokens?|\s*\([0-9,]+\))` after the head h
def sp_ctx(h: String) -> List<&2, List<&2, Tp.It>>:
  +hh = h
  [sp_s(String.append(hh, " of "), sp_more(Tp.CDigC{}, sp_s(" token", []))), sp_s(hh, Tp.Star{Tp.CSp{}} <> sp_s("(", sp_more(Tp.CDigC{}, sp_s(")", []))))]

# R2: the overflow patterns
def sp_overflow_pats() -> List<&2, Tp.Pat>:
  [
    # prompt (?:is )?too long
    sp_anywhere(["prompt is too long", "prompt too long"]),
    # prompt exceeds max length | request_too_large | input is too long
    # for requested model | exceeds the context window
    sp_anywhere(["prompt exceeds max length", "request_too_large", "input is too long for requested model", "exceeds the context window"]),
    # exceeds (?:the )?(?:model'?s )?maximum context length(?: of [0-9,]+
    # tokens?|\s*\([0-9,]+\))
    Tp.Pat{False{}, List.concat(&2, List<&2, Tp.It>, [sp_ctx("exceeds maximum context length"), sp_ctx("exceeds the maximum context length"), sp_ctx("exceeds models maximum context length"), sp_ctx("exceeds the models maximum context length"), sp_ctx("exceeds model's maximum context length"), sp_ctx("exceeds the model's maximum context length")])},
    # input token count.*exceeds the maximum
    Tp.Pat{False{}, [sp_s("input token count", Tp.Star{Tp.CAny{}} <> sp_s("exceeds the maximum", []))]},
    # maximum prompt length is [0-9]+
    Tp.Pat{False{}, [sp_s("maximum prompt length is ", [Tp.One{Tp.CDig{}}])]},
    # reduce the length of the messages
    sp_anywhere(["reduce the length of the messages"]),
    # maximum context length is [0-9]+ tokens
    Tp.Pat{False{}, [sp_s("maximum context length is ", sp_more(Tp.CDig{}, sp_s(" tokens", [])))]},
    # exceeds (?:the )?maximum allowed input length of [0-9,]+ tokens?
    Tp.Pat{False{}, [sp_s("exceeds maximum allowed input length of ", sp_more(Tp.CDigC{}, sp_s(" token", []))), sp_s("exceeds the maximum allowed input length of ", sp_more(Tp.CDigC{}, sp_s(" token", [])))]},
    # input \([0-9]+ tokens\) is longer than the model'?s context length
    # \([0-9]+ tokens\)
    Tp.Pat{False{}, [sp_s("input (", sp_more(Tp.CDig{}, sp_s(" tokens) is longer than the models context length (", sp_more(Tp.CDig{}, sp_s(" tokens)", []))))), sp_s("input (", sp_more(Tp.CDig{}, sp_s(" tokens) is longer than the model's context length (", sp_more(Tp.CDig{}, sp_s(" tokens)", [])))))]},
    # exceeds the limit of [0-9]+
    Tp.Pat{False{}, [sp_s("exceeds the limit of ", [Tp.One{Tp.CDig{}}])]},
    # exceeds the available context size | greater than the context length
    # | context window exceeds limit | exceeded model token limit
    sp_anywhere(["exceeds the available context size", "greater than the context length", "context window exceeds limit", "exceeded model token limit"]),
    # too large for model with [0-9]+ maximum context length
    Tp.Pat{False{}, [sp_s("too large for model with ", sp_more(Tp.CDig{}, sp_s(" maximum context length", [])))]},
    # prompt has [0-9,]+ tokens?, but the configured context size is
    # [0-9,]+ tokens?
    Tp.Pat{False{}, [sp_s("prompt has ", sp_more(Tp.CDigC{}, sp_s(" token, but the configured context size is ", sp_more(Tp.CDigC{}, sp_s(" token", []))))), sp_s("prompt has ", sp_more(Tp.CDigC{}, sp_s(" tokens, but the configured context size is ", sp_more(Tp.CDigC{}, sp_s(" token", [])))))]},
    # model_context_window_exceeded | prompt too long; exceeded (?:max
    # )?context length | range of input length should be
    sp_anywhere(["model_context_window_exceeded", "prompt too long; exceeded context length", "prompt too long; exceeded max context length", "range of input length should be"]),
    # context[_ ]length[_ ]exceeded | too many tokens | token limit exceeded
    sp_anywhere(["context_length_exceeded", "context_length exceeded", "context length_exceeded", "context length exceeded", "too many tokens", "token limit exceeded"])
  ]

# R2: ^4(?:00|13)\s*(?:status code)?\s*\(no body\)
def sp_cerebras() -> Tp.Pat:
  Tp.Pat{True{}, [sp_s("400", Tp.Star{Tp.CSp{}} <> Tp.Star{Tp.CSp{}} <> sp_s("(no body)", [])), sp_s("400", Tp.Star{Tp.CSp{}} <> sp_s("status code", Tp.Star{Tp.CSp{}} <> sp_s("(no body)", []))), sp_s("413", Tp.Star{Tp.CSp{}} <> Tp.Star{Tp.CSp{}} <> sp_s("(no body)", [])), sp_s("413", Tp.Star{Tp.CSp{}} <> sp_s("status code", Tp.Star{Tp.CSp{}} <> sp_s("(no body)", [])))]}

# R2: ^(Throttling error|Service unavailable): | rate limit | too many
# requests
def sp_calm_pats() -> List<&2, Tp.Pat>:
  [Tp.Pat{True{}, [sp_s("throttling error:", []), sp_s("service unavailable:", [])]}, sp_anywhere(["rate limit", "too many requests"])]

def sp_is_error(s: O.Stop) -> Bool:
  match s:
    case O.SError{}:
      True{}
    case O.SStop{}:
      False{}
    case O.SLength{}:
      False{}
    case O.SOther{}:
      False{}

# R1: an error message that reads as an overflow: not empty, nothing calm
# found, and an overflow pattern found (or Cerebras' at the start, from
# Cerebras)
def sp_message(+msg: String, +provider: String) -> Bool:
  +f = TextPat.sp_fold(msg)
  Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, sp_calm_pats())), Bool.or(TextPat.sp_any(f, sp_overflow_pats()), Bool.and(String.eq(provider, "cerebras"), TextPat.sp_any(f, [sp_cerebras()])))))

# R3: the usage of a stop that says the input filled the window
def sp_usage(s: O.Stop, +window: Nat, +used: Nat, output: Nat) -> Bool:
  match s:
    case O.SStop{}:
      Bool.and(Nat.is_lt(0n, window), Nat.is_lt(window, used))
    case O.SLength{}:
      Bool.and(Nat.is_lt(0n, window), Bool.and(Nat.is_eq(output, 0n), Nat.is_le(Nat.sub(window, Nat.div(window, 100n)), used)))
    case O.SOther{}:
      False{}
    case O.SError{}:
      False{}

# R1, R3: whether the reply is an overflow
def sp_overflow(+st: O.Stop, msg: String, provider: String, window: Nat, input: Nat, cache_read: Nat, output: Nat) -> Bool:
  Bool.or(Bool.and(sp_is_error(st), sp_message(msg, provider)), sp_usage(st, window, Nat.add(input, cache_read), output))

# R4: whether a length stop is recoverable
def sp_recoverable(s: O.Stop, +desired: Nat, output: Nat) -> Bool:
  match s:
    case O.SLength{}:
      Bool.and(Nat.is_lt(0n, desired), Nat.is_lt(output, desired))
    case O.SStop{}:
      False{}
    case O.SOther{}:
      False{}
    case O.SError{}:
      False{}

# R5: the spelling of a request and of its reply

def sp_w_stop(s: O.Stop, rest: String) -> String:
  match s:
    case O.SStop{}:
      Wr.put_nat(0n, rest)
    case O.SLength{}:
      Wr.put_nat(1n, rest)
    case O.SOther{}:
      Wr.put_nat(2n, rest)
    case O.SError{}:
      Wr.put_nat(3n, rest)

def sp_w_req(q: FO.Req, rest: String) -> String:
  match q:
    case FO.QOverflow{st, m, p, w, i, c, o}:
      Wr.put_nat(0n, sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, Wr.put_nat(o, rest))))))))
    case FO.QRecoverable{st, d, o}:
      Wr.put_nat(1n, sp_w_stop(st, Wr.put_nat(d, Wr.put_nat(o, rest))))

def sp_w_reply(q: FO.Req) -> String:
  match q:
    case FO.QOverflow{st, m, p, w, i, c, o}:
      Wr.put_bool(sp_overflow(st, m, p, w, i, c, o), "")
    case FO.QRecoverable{st, d, o}:
      Wr.put_bool(sp_recoverable(st, d, o), "")

# every number and length of the request fits the wire
def sp_fit_req(q: FO.Req) -> Bool:
  match q:
    case FO.QOverflow{st, m, p, w, i, c, o}:
      Bool.and(LawsBase.wire_fits(String.length(m)), Bool.and(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))))))
    case FO.QRecoverable{st, d, o}:
      Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(o))

# Laws: the decision
# ------------------

# LAW overflow_decides (R1-R3): whether every reply is an overflow, for
# every stop, message, provider, window and usage, is the spec's
# EXCLUDES: a pattern dropped or changed, a case-sensitive search, a calm
#   message read as an overflow, the Cerebras pattern for another provider
#   or away from the start, an empty message searched, cache reads left
#   out of the usage, a window of 0 used, a silent overflow at the window
#   itself, a 99% bound off by one, a length stop with output read as full
law overflow_decides:
  for +st: O.Stop
  for +msg: String
  for +provider: String
  for +window: Nat
  for +input: Nat
  for +cache_read: Nat
  for +output: Nat
  {O.overflow(st, msg, provider, window, input, cache_read, output) == sp_overflow(st, msg, provider, window, input, cache_read, output) : Bool}

# LAW overflow_recoverable (R4): whether every length stop is recoverable
# is the spec's
# EXCLUDES: a stop other than length recovered, an output at the limit
#   recovered, a limit of 0 read as a limit
law overflow_recoverable:
  for +st: O.Stop
  for +desired: Nat
  for +output: Nat
  {O.recoverable(st, desired, output) == sp_recoverable(st, desired, output) : Bool}

# LAW overflow_message_decides (R1, R2): whether every message reads as an
# overflow from every provider is the spec's
# EXCLUDES: an error message tested another way than the reply's (a
#   pattern, the calm test, the fold or Cerebras' provider dropped or
#   changed only in the message test)
law overflow_message_decides:
  for +msg: String
  for +provider: String
  {O.message_overflow(msg, provider) == sp_message(msg, provider) : Bool}

# LAW overflow_message_found (R1, R2): a message is an overflow, from every
# provider, when its folded text holds, anywhere, a part that matches an
# alternative of an overflow pattern and no calm pattern is found in it:
# whatever text comes before and after that part, in any case
# EXCLUDES: a pattern looked for only at the start or the end of a message,
#   text around the part that hides it, a case-sensitive search, an
#   alternative or a pattern of the table skipped, a provider that changes
#   an overflow pattern's answer
law overflow_message_found:
  for +msg: String
  for +provider: String
  for +a: String
  for +u: String
  for +b: String
  for +pre: List<&2, Tp.Pat>
  for +apre: List<&2, List<&2, Tp.It>>
  for +its: List<&2, Tp.It>
  for +apost: List<&2, List<&2, Tp.It>>
  for +post: List<&2, Tp.Pat>
  for +hp: {sp_overflow_pats() == List.append(&2, Tp.Pat, pre, Tp.Pat{False{}, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post) : List<&2, Tp.Pat>}
  for +hf: {TextPat.sp_fold(msg) == String.append(a, String.append(u, b)) : String}
  for +hu: {TextPat.sp_lang(u, its) == True{} : Bool}
  for +hn: {String.is_empty(u) == False{} : Bool}
  for hc: {TextPat.sp_any(TextPat.sp_fold(msg), sp_calm_pats()) == False{} : Bool}
  {O.message_overflow(msg, provider) == True{} : Bool}

# LAW overflow_message_calm (R1): a message in whose folded text a calm
# pattern is found is no overflow, from every provider, whatever overflow
# pattern it holds too
# EXCLUDES: an overflow pattern that wins over a rate limit or a throttling
#   message, a calm pattern looked for case-sensitively
law overflow_message_calm:
  for +msg: String
  for +provider: String
  for hc: {TextPat.sp_any(TextPat.sp_fold(msg), sp_calm_pats()) == True{} : Bool}
  {O.message_overflow(msg, provider) == False{} : Bool}

# LAW overflow_message_example (R1, R2): anchor: short messages of the Rust
# tests (the text around a pattern is overflow_message_found's): z.ai (two
# spellings, folded case), a crash, a calm throttling message, Cerebras'
# bodyless 400 only for Cerebras
# EXCLUDES: a pattern table that drifts from the regexes it replaced
law overflow_message_example:
  {[O.message_overflow("Prompt too long", "zai"), O.message_overflow("PROMPT exceeds max length", "zai"), O.message_overflow("model runner crashed", "ollama"), O.message_overflow("Throttling error: too many tokens", "x"), O.message_overflow("400 status code (no body)", "cerebras"), O.message_overflow("400 status code (no body)", "opencode-go")] == [True{}, True{}, False{}, False{}, True{}, False{}] : List<&2, Bool>}

# LAW overflow_message_context_example (R1, R2): anchor: the context-length
# messages of the Rust tests, cut to the pattern: Together AI, a proxy, DS4
# with commas
# EXCLUDES: a pattern table that drifts from the regexes it replaced
law overflow_message_context_example:
  {[O.message_overflow("input (5 tokens) is longer than the model's context length (2 tokens)", "x"), O.message_overflow("exceeds model's maximum context length (26)", "x"), O.message_overflow("prompt has 5,958 tokens, but the configured context size is 2,560 tokens", "x")] == [True{}, True{}, True{}] : List<&2, Bool>}

# LAW overflow_usage_example (R3, R4): anchor: a silent overflow, a length
# stop at 99% and just below it, windows of 150 and 99, a length stop with
# output, no window, recoverable stops
# EXCLUDES: a 99% bound computed another way
law overflow_usage_example:
  {[O.overflow(O.SStop{}, "", "x", 100n, 60n, 41n, 5n), O.overflow(O.SStop{}, "", "x", 100n, 60n, 40n, 5n), O.overflow(O.SLength{}, "", "x", 100n, 9n, 90n, 0n), O.overflow(O.SLength{}, "", "x", 100n, 8n, 90n, 0n), O.overflow(O.SLength{}, "", "x", 150n, 149n, 0n, 0n), O.overflow(O.SLength{}, "", "x", 150n, 148n, 0n, 0n), O.overflow(O.SLength{}, "", "x", 99n, 99n, 0n, 0n), O.overflow(O.SLength{}, "", "x", 100n, 99n, 0n, 4n), O.overflow(O.SLength{}, "", "x", 0n, 99n, 0n, 0n), O.recoverable(O.SLength{}, 128n, 16n), O.recoverable(O.SLength{}, 16n, 16n), O.recoverable(O.SStop{}, 128n, 16n)] == [True{}, False{}, True{}, False{}, True{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}] : List<&2, Bool>}

# Laws: the entry (R5)
# --------------------

# LAW overflow_entry_answers (R5): the entry answers every request Rust
# spells, every number and length within the wire, with the spelled answer
# of the spec
# EXCLUDES: the fields read in another order, a stop read as another, a
#   default
law overflow_entry_answers:
  for +q: FO.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FO.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW overflow_entry_reads (R5): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law overflow_entry_reads:
  for +q: FO.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FO.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FO.Req>}

# LAW overflow_entry_exact (R5): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question or
#   stop, a malformed field, input left over)
law overflow_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FO.ffi(s)) == False{} : Bool}
  exs r: FO.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW overflow_entry_refuses (R5): every error the entry answers is exactly
# `E overflow: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law overflow_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FO.ffi(s)) == True{} : Bool}
  {FO.ffi(s) == Wr.err("overflow: malformed request") : String}

# LAW overflow_entry_example (R5): anchor: the wire strings Rust sends and
# the replies it reads; an unknown stop, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law overflow_entry_example:
  {[FO.ffi("0,3,15,Prompt too long3,zai0,0,0,0,"), FO.ffi("0,0,0,1,x100,60,41,5,"), FO.ffi("1,1,128,16,"), FO.ffi("1,4,128,16,"), FO.ffi("1,1,128,16,x")] == ["T", "T", "T", Wr.err("overflow: malformed request"), Wr.err("overflow: malformed request")] : List<&2, String>}
