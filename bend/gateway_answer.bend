# gateway_answer: what a settled session event tells the Signal peer that
# holds the floor (Rust: crates/eukhe-gateway answer.rs, called by
# gateway.rs for every event of the bound session): the agent's text, a
# failure, a stop, or nothing.
#
# - A run that ends with no assistant message at all (no model
#   configured, a request that never started) answers `no_model()`.
# - A settled assistant message: on stop or length, its text blocks joined
#   by a blank line, unless that text is only whitespace (then nothing);
#   on error, its error message on one line; on abort, a stop; on a
#   tool-use step, nothing.
# - A turn that faulted without an assistant message answers its error on
#   one line.
# - Every other event answers nothing.
# One line: the words of the reason (split at Rust's whitespace, the
# Unicode White_Space set) joined by single spaces; a missing or blank
# reason is `request_failed()`. Pure: no IO, no @unsafe.

import Base

# Why an assistant message stopped
type Stop is Data:
  SStop{}
  SLength{}
  SError{}
  SAborted{}
  SToolUse{}

# What Rust saw of one session event
type Ev is Data:
  # the run ended; whether any of its messages is an assistant message
  EAgentEnd{assistant: Bool}
  # an assistant message settled: its stop, its text blocks, its error
  EAssistant{stop: Stop, texts: List<&2, String>, error: Maybe<&2, String>}
  # a turn ended: whether it carries an assistant message, and its error
  ETurnEnd{answered: Bool, error: Maybe<&2, String>}
  # any other event
  EOther{}

# What the peer is told
type Answer is Data:
  ANone{}
  AText{text: String}
  AFailed{reason: String}
  AStopped{}

# What a run that ended before the model answered tells the phone
def no_model() -> String:
  "the turn ended before the model answered. Send /status to see the model"

# The reason of a failure that names none
def request_failed() -> String:
  "the model request failed"

# Text
# ----

# Rust's whitespace (`char::is_whitespace`), by code point
def spaces() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), in(x, rest))

# c is whitespace
def space(c: Char) -> Bool:
  in(Char.to_u32(c), spaces())

# s is only whitespace (or empty)
def blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(space(c), blank(t))

# s starts with a char that is no whitespace
def worded(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.not(space(c))

def words.glue(c: Char, ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      [SCon{c, SNil{}}]
    case w <> rest:
      SCon{c, w} <> rest

def words.at(sp: Bool, joins: Bool, c: Char, ws: List<&2, String>) -> List<&2, String>:
  match sp:
    case True{}:
      ws
    case False{}:
      match joins:
        case True{}:
          words.glue(c, ws)
        case False{}:
          SCon{c, SNil{}} <> ws

# the words of s (Rust `split_whitespace`)
def words(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{+c, +t}:
      words.at(space(c), worded(t), c, words(t))

def join.rest(+sep: String, ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      SNil{}
    case w <> rest:
      String.append(sep, String.append(w, join.rest(sep, rest)))

# ws joined by sep
def join(+sep: String, ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      SNil{}
    case w <> rest:
      String.append(w, join.rest(sep, rest))

# s on one line: its words joined by single spaces
def line(s: String) -> String:
  join(" ", words(s))

def reason.of(+s: String, b: Bool) -> String:
  match b:
    case True{}:
      request_failed()
    case False{}:
      line(s)

# a failure's reason on one line; a missing or blank one names the failure
def reason(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      request_failed()
    case Some{+s}:
      reason.of(s, blank(s))

# Answers
# -------

def text.of(+t: String, b: Bool) -> Answer:
  match b:
    case True{}:
      ANone{}
    case False{}:
      AText{t}

# the text blocks of a message, joined by a blank line, unless only
# whitespace
def text(ts: List<&2, String>) -> Answer:
  +t = join("\n\n", ts)
  text.of(t, blank(t))

def assistant(s: Stop, ts: List<&2, String>, e: Maybe<&2, String>) -> Answer:
  match s:
    case SStop{}:
      text(ts)
    case SLength{}:
      text(ts)
    case SError{}:
      AFailed{reason(e)}
    case SAborted{}:
      AStopped{}
    case SToolUse{}:
      ANone{}

def turn(answered: Bool, e: Maybe<&2, String>) -> Answer:
  match answered:
    case True{}:
      ANone{}
    case False{}:
      match e:
        case None{}:
          ANone{}
        case Some{r}:
          AFailed{reason(Some{r})}

# the answer an event carries
def answer(ev: Ev) -> Answer:
  match ev:
    case EAgentEnd{a}:
      match a:
        case True{}:
          ANone{}
        case False{}:
          AFailed{no_model()}
    case EAssistant{s, ts, e}:
      assistant(s, ts, e)
    case ETurnEnd{a, e}:
      turn(a, e)
    case EOther{}:
      ANone{}
