# compaction_cut: where a compaction cuts the model context of a
# conversation, and what the summarizer's answer is (the Rust host is
# crates/eukhe-durable/src/harness/compaction/range.rs `select_cut` and
# compaction/prompt.rs `summary_text`, `summary_failure`; the durable
# harness spec §8.7).
#
# Facts. The host gives each contribution of the context (an active
# entry's messages, the head marker's first when there is one) as its
# estimated tokens (a Nat) and its messages' facts (bend/context_order.bend
# Msg: user, system, an assistant with its stop reason and call ids, a
# tool result with its call id; ids interned to Nats). The threshold is
# a Limit: Below{k} keeps walking while the tokens kept are fewer than k;
# Never walks to the start (the host turns its f64 keep window into it:
# NaN and k <= 0 are Below{0}, +infinity is Never, else Below{ceil(k)}).
#
# cut: walking back from the last contribution to the first after the
# marker, the tokens kept add up until they reach the limit at some
# contribution; the cut is the first candidate at or after it, else the
# last candidate; none when the limit is never reached, when there is no
# candidate, or when every contribution after the marker and before the
# cut is empty (nothing to summarize). A contribution is a candidate when
# its first message is an assistant answer, or a user message that no
# result of the calls of the last assistant answer before it follows
# (until the next assistant answer); a contribution that starts with a
# system message, a tool result, or nothing is no candidate.
#
# summary: the summarizer's answer is a summary when it stopped as stop,
# called no tool and has text that is not blank (the host trims it as
# JS does); else a failure with its text: an error or aborted answer
# "Summarization failed: " and its error message (else its stop reason),
# a length answer that it hit the token limit, one with a tool call that
# it called a tool, else that it produced no text.
#
# Pure: no IO, no @unsafe. laws/compaction_cut.bend states its laws.

import Base
import ./context_order.bend as Co

# Facts
# -----

# when the walk back stops
type Limit is Data:
  # never: the walk reaches the first contribution
  Never{}
  # once the tokens kept are k or more
  Below{k: Nat}

# a contribution: its estimated tokens and its messages
type Contrib is Data:
  Contrib{tokens: Nat, msgs: List<&2, Co.Msg>}

# Answers
# -------

# the summarizer's answer
type Outcome is Data:
  Summary{}
  Failed{text: String}

# the walk back so far: the limit reached at a contribution, or the tokens
# kept
type Walk is Data:
  Reached{at: Nat}
  Kept{n: Nat}

# The walk back
# -------------

def reach.pick(b: Bool, n: Nat, i: Nat) -> Walk:
  match b:
    case True{}:
      Kept{n}
    case False{}:
      Reached{i}

# contribution i with t tokens after the walk over the later ones kept n:
# skipped before the start, else its tokens are kept too
def reach.at(skip: Bool, +n: Nat, t: Nat, i: Nat, +k: Nat) -> Walk:
  match skip:
    case True{}:
      Kept{n}
    case False{}:
      +m = Nat.add(n, t)
      reach.pick(Nat.is_lt(m, k), m, i)

def reach.step(w: Walk, t: Nat, skip: Bool, i: Nat, +k: Nat) -> Walk:
  match w:
    case Reached{a}:
      Reached{a}
    case Kept{n}:
      reach.at(skip, n, t, i, k)

# the walk back over cs (the first at index i) down to the start
def reach.go(cs: List<&2, Contrib>, +i: Nat, +start: Nat, +k: Nat) -> Walk:
  match cs:
    case Nil{}:
      Kept{0n}
    case c <> t:
      match c:
        case Contrib{tok, ms}:
          reach.step(reach.go(t, 1n+i, start, k), tok, Nat.is_lt(i, start), i, k)

def reach.of(w: Walk) -> Maybe<&2, Nat>:
  match w:
    case Reached{a}:
      Some{a}
    case Kept{n}:
      None{}

# the contribution where the walk back from the end reaches the limit
def reach(+start: Nat, lim: Limit, cs: List<&2, Contrib>) -> Maybe<&2, Nat>:
  match lim:
    case Never{}:
      None{}
    case Below{k}:
      reach.of(reach.go(cs, 0n, start, k))

# Candidates
# ----------

# the calls of the last assistant answer of ms, else last
def last_calls(ms: List<&2, Co.Msg>, last: List<&2, Nat>) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      last
    case m <> t:
      match m:
        case Co.MUser{}:
          last_calls(t, last)
        case Co.MSystem{}:
          last_calls(t, last)
        case Co.MAsst{s, cs}:
          last_calls(t, cs)
        case Co.MRes{c}:
          last_calls(t, last)

def has(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, c), has(t, c))

# no result of the calls comes in ms before the next assistant answer
def ahead.last(ms: List<&2, Co.Msg>, +calls: List<&2, Nat>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> u:
      match m:
        case Co.MUser{}:
          ahead.last(u, calls)
        case Co.MSystem{}:
          ahead.last(u, calls)
        case Co.MAsst{s, xs}:
          True{}
        case Co.MRes{d}:
          Bool.and(Bool.not(has(calls, d)), ahead.last(u, calls))

# no result of the calls comes in ms, then the contributions cs, before
# the next assistant answer (ms: the rest of the contribution before cs)
def ahead(cs: List<&2, Contrib>, ms: List<&2, Co.Msg>, +calls: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      ahead.last(ms, calls)
    case c <> +t:
      match c:
        case Contrib{+tok, +ms2}:
          match ms:
            case Nil{}:
              ahead(t, ms2, calls)
            case m <> u:
              match m:
                case Co.MUser{}:
                  ahead(Contrib{tok, ms2} <> t, u, calls)
                case Co.MSystem{}:
                  ahead(Contrib{tok, ms2} <> t, u, calls)
                case Co.MAsst{s, xs}:
                  True{}
                case Co.MRes{d}:
                  Bool.and(Bool.not(has(calls, d)), ahead(Contrib{tok, ms2} <> t, u, calls))

def cand.user(calls: List<&2, Nat>, u: List<&2, Co.Msg>, rest: List<&2, Contrib>) -> Bool:
  match calls:
    case Nil{}:
      True{}
    case x <> xs:
      ahead(rest, u, x <> xs)

# the contribution with messages ms, before the contributions rest, the
# calls of the last assistant before it being calls, is a candidate
def cand(ms: List<&2, Co.Msg>, calls: List<&2, Nat>, rest: List<&2, Contrib>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> u:
      match m:
        case Co.MUser{}:
          cand.user(calls, u, rest)
        case Co.MSystem{}:
          False{}
        case Co.MAsst{s, xs}:
          True{}
        case Co.MRes{c}:
          False{}

def cands.one(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> rest
    case False{}:
      rest

# the candidates among cs (the first at index i) from the start, last
# being the calls of the last assistant answer before cs
def cands.go(cs: List<&2, Contrib>, +i: Nat, +start: Nat, +last: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case c <> +t:
      match c:
        case Contrib{tok, +ms}:
          cands.one(Bool.and(Bool.not(Nat.is_lt(i, start)), cand(ms, last, t)), i, cands.go(t, 1n+i, start, last_calls(ms, last)))

# the candidates of cs from the start
def cands(+start: Nat, cs: List<&2, Contrib>) -> List<&2, Nat>:
  cands.go(cs, 0n, start, [])

# The cut
# -------

def first_at.pick(b: Bool, x: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

# the first of xs at or after r
def first_at(xs: List<&2, Nat>, +r: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case +x <> t:
      first_at.pick(Bool.not(Nat.is_lt(x, r)), x, first_at(t, r))

def last_of.go(xs: List<&2, Nat>, last: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      last
    case x <> t:
      last_of.go(t, Some{x})

def pick_cut.or(m: Maybe<&2, Nat>, +xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      last_of.go(xs, None{})
    case Some{x}:
      Some{x}

# the first candidate at or after r, else the last candidate
def pick_cut(+xs: List<&2, Nat>, +r: Nat) -> Maybe<&2, Nat>:
  pick_cut.or(first_at(xs, r), xs)

def nonempty(ms: List<&2, Co.Msg>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> t:
      True{}

# some contribution of cs (the first at index i) from the start and
# before x has messages
def filled(cs: List<&2, Contrib>, +i: Nat, +start: Nat, +x: Nat) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      match c:
        case Contrib{tok, ms}:
          Bool.or(Bool.and(Bool.and(Bool.not(Nat.is_lt(i, start)), Nat.is_lt(i, x)), nonempty(ms)), filled(t, 1n+i, start, x))

def cut.keep(b: Bool, x: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def cut.at(m: Maybe<&2, Nat>, +start: Nat, cs: List<&2, Contrib>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      cut.keep(filled(cs, 0n, start, x), x)

def cut.from(r: Maybe<&2, Nat>, +start: Nat, +cs: List<&2, Contrib>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      None{}
    case Some{a}:
      cut.at(pick_cut(cands(start, cs), a), start, cs)

def start_of(head: Bool) -> Nat:
  match head:
    case True{}:
      1n
    case False{}:
      0n

# the index of the first contribution a compaction keeps, if it cuts
def cut(head: Bool, lim: Limit, +cs: List<&2, Contrib>) -> Maybe<&2, Nat>:
  +start = start_of(head)
  cut.from(reach(start, lim, cs), start, cs)

# The summarizer's answer
# -----------------------

def name(s: Co.Stop) -> String:
  match s:
    case Co.SPending{}:
      "pending"
    case Co.SStop{}:
      "stop"
    case Co.SLength{}:
      "length"
    case Co.SToolUse{}:
      "toolUse"
    case Co.SError{}:
      "error"
    case Co.SAborted{}:
      "aborted"
    case Co.SDeferred{}:
      "deferred"

def failed.reason(s: Co.Stop, err: Maybe<&2, String>) -> String:
  match err:
    case None{}:
      name(s)
    case Some{e}:
      e

def failed.as(s: Co.Stop, err: Maybe<&2, String>) -> Outcome:
  Failed{String.append("Summarization failed: ", failed.reason(s, err))}

def failed.call(calls: Bool) -> Outcome:
  match calls:
    case True{}:
      Failed{"Summarization attempted to call a tool"}
    case False{}:
      Failed{"Summarization produced no text"}

# the failure of an answer that is no summary
def failed(s: Co.Stop, calls: Bool, err: Maybe<&2, String>) -> Outcome:
  match s:
    case Co.SPending{}:
      failed.call(calls)
    case Co.SStop{}:
      failed.call(calls)
    case Co.SLength{}:
      Failed{"Summarization hit the token limit; the summary is incomplete"}
    case Co.SToolUse{}:
      failed.call(calls)
    case Co.SError{}:
      failed.as(Co.SError{}, err)
    case Co.SAborted{}:
      failed.as(Co.SAborted{}, err)
    case Co.SDeferred{}:
      failed.call(calls)

def summary.text(b: Bool, s: Co.Stop, calls: Bool, err: Maybe<&2, String>) -> Outcome:
  match b:
    case True{}:
      Summary{}
    case False{}:
      failed(s, calls, err)

def is_stop(s: Co.Stop) -> Bool:
  match s:
    case Co.SPending{}:
      False{}
    case Co.SStop{}:
      True{}
    case Co.SLength{}:
      False{}
    case Co.SToolUse{}:
      False{}
    case Co.SError{}:
      False{}
    case Co.SAborted{}:
      False{}
    case Co.SDeferred{}:
      False{}

# the summarizer's answer: its stop reason, whether it called a tool,
# whether its trimmed text is not blank, its error message
def summary(+s: Co.Stop, +calls: Bool, text: Bool, err: Maybe<&2, String>) -> Outcome:
  summary.text(Bool.and(is_stop(s), Bool.and(Bool.not(calls), text)), s, calls, err)
