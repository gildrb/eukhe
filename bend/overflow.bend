# overflow: whether a model reply is a context overflow (Rust: eukhe-ai
# utils/overflow.rs `is_context_overflow`, `is_recoverable_length`;
# laws/overflow.bend). Three ways:
# 1. an error reply whose message a provider writes for an input past the
#    model's window (one pattern per provider; Cerebras overflows as a
#    bodyless 400/413), unless the message reads as a rate limit or a
#    server error;
# 2. a silent overflow (z.ai): a stop whose input usage passes the window;
# 3. a length stop with no output and the input filling 99% of the window
#    (Xiaomi MiMo).
# The search is case-insensitive (bend/text_pat.bend `fold`). Pure: no IO,
# no @unsafe.

import Base
import ./text_pat.bend as Tp

# How the reply stopped
type Stop is Data:
  SStop{}
  SLength{}
  # a tool use or an abort
  SOther{}
  SError{}

# Patterns
# --------

# the chars of s, one item each, before rest
def lit(s: String, rest: List<&2, Tp.It>) -> List<&2, Tp.It>:
  match s:
    case SNil{}:
      rest
    case SCon{c, t}:
      Tp.One{Tp.CLit{c}} <> lit(t, rest)

# one or more of a class (regex `x+`), before rest
def plus(+c: Tp.Cls, rest: List<&2, Tp.It>) -> List<&2, Tp.It>:
  Tp.One{c} <> Tp.Star{c} <> rest

def dig() -> Tp.Cls:
  Tp.CDig{}

def digc() -> Tp.Cls:
  Tp.CDigC{}

# a pattern found anywhere, of literal alternatives
def lits.go(xs: List<&2, String>) -> List<&2, List<&2, Tp.It>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      lit(x, []) <> lits.go(t)

def lits(xs: List<&2, String>) -> Tp.Pat:
  Tp.Pat{False{}, lits.go(xs)}

def any_of(alts: List<&2, List<&2, Tp.It>>) -> Tp.Pat:
  Tp.Pat{False{}, alts}

# The messages providers write for an input past the window, lowercase:
# each regex of overflow.rs as its alternatives
def overflow_pats() -> List<&2, Tp.Pat>:
  [
    # prompt (?:is )?too long: Anthropic and z.ai token overflow
    lits(["prompt is too long", "prompt too long"]),
    # z.ai CN endpoint; Anthropic byte-size overflow (HTTP 413); Amazon
    # Bedrock; OpenAI (Completions & Responses API)
    lits(["prompt exceeds max length", "request_too_large", "input is too long for requested model", "exceeds the context window"]),
    # exceeds (?:the )?(?:model'?s )?maximum context length(?: of [0-9,]+
    # tokens?|\s*\([0-9,]+\)): OpenAI-compatible proxies (LiteLLM)
    any_of([
      lit("exceeds maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", [])))),
      lit("exceeds the maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds the maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", [])))),
      lit("exceeds models maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds models maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", [])))),
      lit("exceeds the models maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds the models maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", [])))),
      lit("exceeds model's maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds model's maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", [])))),
      lit("exceeds the model's maximum context length of ", plus(digc(), lit(" token", []))),
      lit("exceeds the model's maximum context length", Tp.Star{Tp.CSp{}} <> lit("(", plus(digc(), lit(")", []))))
    ]),
    # input token count.*exceeds the maximum: Google (Gemini)
    any_of([lit("input token count", Tp.Star{Tp.CAny{}} <> lit("exceeds the maximum", []))]),
    # maximum prompt length is [0-9]+: xAI (Grok)
    any_of([lit("maximum prompt length is ", [Tp.One{dig()}])]),
    # reduce the length of the messages: Groq
    lits(["reduce the length of the messages"]),
    # maximum context length is [0-9]+ tokens: OpenRouter (most backends)
    any_of([lit("maximum context length is ", plus(dig(), lit(" tokens", [])))]),
    # exceeds (?:the )?maximum allowed input length of [0-9,]+ tokens?:
    # OpenRouter/Poolside
    any_of([
      lit("exceeds maximum allowed input length of ", plus(digc(), lit(" token", []))),
      lit("exceeds the maximum allowed input length of ", plus(digc(), lit(" token", [])))
    ]),
    # input \([0-9]+ tokens\) is longer than the model'?s context length
    # \([0-9]+ tokens\): Together AI
    any_of([
      lit("input (", plus(dig(), lit(" tokens) is longer than the models context length (", plus(dig(), lit(" tokens)", []))))),
      lit("input (", plus(dig(), lit(" tokens) is longer than the model's context length (", plus(dig(), lit(" tokens)", [])))))
    ]),
    # exceeds the limit of [0-9]+: GitHub Copilot
    any_of([lit("exceeds the limit of ", [Tp.One{dig()}])]),
    # llama.cpp server; LM Studio; MiniMax; Kimi For Coding
    lits(["exceeds the available context size", "greater than the context length", "context window exceeds limit", "exceeded model token limit"]),
    # too large for model with [0-9]+ maximum context length: Mistral
    any_of([lit("too large for model with ", plus(dig(), lit(" maximum context length", [])))]),
    # prompt has [0-9,]+ tokens?, but the configured context size is
    # [0-9,]+ tokens?: DS4 server
    any_of([
      lit("prompt has ", plus(digc(), lit(" token, but the configured context size is ", plus(digc(), lit(" token", []))))),
      lit("prompt has ", plus(digc(), lit(" tokens, but the configured context size is ", plus(digc(), lit(" token", [])))))
    ]),
    # z.ai finish_reason surfaced as error text; Ollama (prompt too long;
    # exceeded (?:max )?context length); DashScope / Qwen Token Plan
    lits(["model_context_window_exceeded", "prompt too long; exceeded context length", "prompt too long; exceeded max context length", "range of input length should be"]),
    # context[_ ]length[_ ]exceeded, too many tokens, token limit exceeded:
    # generic fallbacks
    lits(["context_length_exceeded", "context_length exceeded", "context length_exceeded", "context length exceeded", "too many tokens", "token limit exceeded"])
  ]

# ^4(?:00|13)\s*(?:status code)?\s*\(no body\): Cerebras' bodyless 400/413
def cerebras_pat() -> Tp.Pat:
  +sp = {Tp.Star{Tp.CSp{}} : Tp.It}
  Tp.Pat{True{}, [
    lit("400", sp <> sp <> lit("(no body)", [])),
    lit("400", sp <> lit("status code", sp <> lit("(no body)", []))),
    lit("413", sp <> sp <> lit("(no body)", [])),
    lit("413", sp <> lit("status code", sp <> lit("(no body)", [])))
  ]}

# Messages that are no overflow even where an overflow pattern matches
# (Bedrock's "ThrottlingException: Too many tokens, please wait ..."):
# ^(Throttling error|Service unavailable): (formatBedrockError prefixes),
# rate limit, too many requests
def calm_pats() -> List<&2, Tp.Pat>:
  [Tp.Pat{True{}, [lit("throttling error:", []), lit("service unavailable:", [])]}, lits(["rate limit", "too many requests"])]

# The decision
# ------------

def is_error(s: Stop) -> Bool:
  match s:
    case SError{}:
      True{}
    case SStop{}:
      False{}
    case SLength{}:
      False{}
    case SOther{}:
      False{}

def is_stop(s: Stop) -> Bool:
  match s:
    case SStop{}:
      True{}
    case SLength{}:
      False{}
    case SOther{}:
      False{}
    case SError{}:
      False{}

def is_length(s: Stop) -> Bool:
  match s:
    case SLength{}:
      True{}
    case SStop{}:
      False{}
    case SOther{}:
      False{}
    case SError{}:
      False{}

# whether an error message reads as an overflow from `provider` (lazy:
# an empty or calm message is not searched further)
def message_overflow(+msg: String, +provider: String) -> Bool:
  +f = Tp.fold_str(msg)
  Tp.pm.and(Bool.not(String.is_empty(msg)), u => Tp.pm.and(Bool.not(Tp.any(f, calm_pats())), v => Tp.pm.or(Tp.any(f, overflow_pats()), w => Tp.pm.and(String.eq(provider, "cerebras"), x => Tp.hit(f, cerebras_pat())))))

# whether the usage says the input filled the window (cases 2 and 3; a
# window of 0 is unknown): input + cache reads past the window on a stop,
# or at least 99% of it on a length stop with no output
def usage_overflow(+stop: Stop, +window: Nat, +input: Nat, output: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, window), Bool.or(Bool.and(is_stop(stop), Nat.is_lt(window, input)), Bool.and(is_length(stop), Bool.and(Nat.is_eq(output, 0n), Nat.is_le(Nat.sub(window, Nat.div(window, 100n)), input)))))

# whether the reply is a context overflow
def overflow(+stop: Stop, msg: String, provider: String, window: Nat, input: Nat, cache_read: Nat, output: Nat) -> Bool:
  Bool.or(Bool.and(is_error(stop), message_overflow(msg, provider)), usage_overflow(stop, window, Nat.add(input, cache_read), output))

# whether a length stop ended below the intended output limit `desired`
# (context pressure or provider truncation, worth one compact-and-retry)
def recoverable(stop: Stop, +desired: Nat, output: Nat) -> Bool:
  Bool.and(is_length(stop), Bool.and(Nat.is_lt(0n, desired), Nat.is_lt(output, desired)))
