# stop: the Directors at a candidate stop of the run loop (the Rust host
# is crates/eukhe-durable/src/harness/generation/stop.rs; laws/stop.bend
# states the laws, spec/harness/stop.bend the spec they refine). A
# candidate stop is a model reply that ends the model's turn with no tool
# call. As omp2's Directors (ADR 0015), the run walks a stack of Directors
# at it, inside to outside; each gives a verdict:
#
# - Pass: the next Director decides;
# - Continue: the run goes on, with the Director's reminder at the end of
#   the next request (a harness note, never logged as the user's words);
#   bend/run/recovery.bend counts each Director's reminders in a row and
#   stops it at its cap;
# - Yield: the stop stands.
#
# With every Director passing, the stop stands: the reply is the final
# answer. The Directors, inside to outside:
#
# - LengthStop: the reply hit the output limit: its text, if any, was cut,
#   so it is never the answer;
# - EmptyStop: no text: nothing the user can read (a thinking-only reply);
# - MarkupStop: tool-call markup in the text that the harness could not
#   read: a call the model meant to make, never an answer;
# - PendingWork: the session owns running work (jobs, children, workflow
#   runs): the stop is a pause, their ends wake the session;
# - UnexpectedStop: the end of the text announces a next step (I'll, let
#   me, next I, now running, ...) and asks the user nothing.
#
# The text tests are mechanical (no judge model) and use explicit phrase
# tables (bend/phrase.bend), no regex. Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as Tp
import ./phrase.bend as P
import ./retry_note.bend as Rn

# The facts of a candidate stop
# -----------------------------

# cut: the reply hit the output limit (stop reason length); text: a text
# block that is not blank; broken: tool-call markup in the text that the
# harness could not read; pending: the session owns running work; said:
# the reply's text
type Facts is Data:
  Facts{cut: Bool, text: Bool, broken: Bool, pending: Bool, said: String}

# The Directors
type Dir is Data:
  LengthStop{}
  EmptyStop{}
  MarkupStop{}
  PendingWork{}
  UnexpectedStop{}

type Verdict is Data:
  Pass{}
  Continue{}
  Yield{}

# what the walk picks: the stop stands, or the Director d continues the run
type Pick is Data:
  Stands{}
  Goes{d: Dir}

# The text tests
# --------------

# the chars of the end of a reply that the text tests read: an
# announcement of a next step ends the reply
def tail_len() -> Nat:
  400n

# s without its first k chars
def drop(k: Nat, s: String) -> String:
  match k:
    case 0n:
      s
    case 1n+j:
      match s:
        case SNil{}:
          SNil{}
        case SCon{c, t}:
          drop(j, t)

# the last n chars of s (all of s when it is shorter)
def tail(+n: Nat, +s: String) -> String:
  drop(Nat.sub(String.length(s), n), s)

# the end of the reply, folded (A-Z as a-z): what the tables are searched in
def heard(+said: String) -> String:
  Tp.fold_str(tail(tail_len(), said))

# the apostrophe items: ' (U+0027) and the right single quote (U+2019)
def apos.ascii() -> P.It:
  P.One{P.CIn{39, 39}}

def apos.curly() -> P.It:
  P.One{P.CIn{8217, 8217}}

# a, an apostrophe, then b, starting a word: both apostrophes
def contracted(a: String, b: String, rest: List<&2, P.Ph>) -> List<&2, P.Ph>:
  +x = a
  +y = b
  P.word_start(P.lit(x, apos.ascii() <> P.lit(y, []))) <> P.word_start(P.lit(x, apos.curly() <> P.lit(y, []))) <> rest

# each text of xs starting a word, before rest
def starts(xs: List<&2, String>, rest: List<&2, P.Ph>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      P.word_start(P.lit(x, [])) <> starts(t, rest)

# the announcements of a next step, all lowercase, each starting a word
def promise_phs() -> List<&2, P.Ph>:
  contracted("i", "ll ", contracted("we", "ll ", contracted("i", "m going to ", contracted("i", "m about to ", contracted("let", "s ", starts(["i will ", "we will ", "i am going to ", "let me ", "next, i ", "next i ", "now running", "now i ", "then i "], []))))))

# the questions to the user: a question mark anywhere (also the fullwidth
# one, U+FF1F), or one of these phrases starting a word
def ask_phs() -> List<&2, P.Ph>:
  P.anywhere([P.One{P.CIn{63, 63}}]) <> P.anywhere([P.One{P.CIn{65311, 65311}}]) <> starts(["let me know", "let us know", "would you like", "do you want", "should i ", "shall i ", "please confirm", "can you confirm", "your call"], [])

# the end of the reply announces a next step
def promises(+said: String) -> Bool:
  P.any(heard(said), promise_phs())

# the end of the reply asks the user something
def asks(+said: String) -> Bool:
  P.any(heard(said), ask_phs())

# The walk
# --------

def on(b: Bool) -> Verdict:
  match b:
    case True{}:
      Continue{}
    case False{}:
      Pass{}

def hold(b: Bool) -> Verdict:
  match b:
    case True{}:
      Yield{}
    case False{}:
      Pass{}

# the facts, one by one
def Facts.cut(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, said}:
      cut

def Facts.text(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, said}:
      text

def Facts.broken(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, said}:
      broken

def Facts.pending(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, said}:
      pending

def Facts.said(f: Facts) -> String:
  match f:
    case Facts{cut, text, broken, pending, said}:
      said

# the verdict of the Director d at the stop f
def verdict(d: Dir, +f: Facts) -> Verdict:
  match d:
    case LengthStop{}:
      on(Facts.cut(f))
    case EmptyStop{}:
      on(Bool.not(Facts.text(f)))
    case MarkupStop{}:
      on(Facts.broken(f))
    case PendingWork{}:
      hold(Facts.pending(f))
    case UnexpectedStop{}:
      +said = Facts.said(f)
      on(Bool.and(promises(said), Bool.not(asks(said))))

# the stack, inside to outside
def stack() -> List<&2, Dir>:
  [LengthStop{}, EmptyStop{}, MarkupStop{}, PendingWork{}, UnexpectedStop{}]

# the verdict v of d: Pass asks the next Directors (lazy)
def pick(v: Verdict, d: Dir, next: Unit -> Pick) -> Pick:
  match v:
    case Pass{}:
      next(Unit{})
    case Continue{}:
      Goes{d}
    case Yield{}:
      Stands{}

def walk.go(ds: List<&2, Dir>, +f: Facts) -> Pick:
  match ds:
    case Nil{}:
      Stands{}
    case +d <> rest:
      pick(verdict(d, f), d, u => walk.go(rest, f))

# the walk at the stop f: the first Director that does not pass decides
def walk(+f: Facts) -> Pick:
  walk.go(stack(), f)

# Caps
# ----

# the reminders in a row of EmptyStop and of UnexpectedStop (omp
# EMPTY_STOP_MAX_RETRIES, the unexpected-stop cap); LengthStop and
# MarkupStop keep the caps of their recoveries (LENGTH_NOTES, LEAK_NOTES)
def empty_cap() -> Nat:
  3n

def promise_cap() -> Nat:
  3n

# The reminders
# -------------

# the reminders this module writes: a length stop with text (`tokens` the
# limit, 0: not reported; the length note `row` of `cap`), an announced
# step not taken (the stop note `row`)
type Note is Data:
  Cut{tokens: Nat, row: Nat, cap: Nat}
  Promised{row: Nat}

def note.body(n: Note) -> String:
  match n:
    case Cut{t, r, k}:
      String.concat(["your previous reply hit ", Rn.limit(t), " before it finished, so the harness did not take its cut text as your answer. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with further edits in this turn. Length note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Promised{r}:
      String.concat(["you announced more work but ended the turn. The task is incomplete: call the next concrete tool now. If the task is done, give the final answer without announcing more work. Stop note ", Nat.show(r), " of ", Nat.show(promise_cap()), "."])

# the text of the note of the request of `attempt`
def note(attempt: Nat, n: Note) -> String:
  String.append("Harness note, attempt ", String.append(Nat.show(attempt), String.append(": ", note.body(n))))

# The round cap
# -------------

# the tool rounds left at which a request tells the model how many remain
def low() -> Nat:
  10n

# the tool rounds whose results the model still reads, after `done` of the
# run's `max` (maxToolRounds): the round that reaches the cap ends the run
def left(+max: Nat, +done: Nat) -> Nat:
  Nat.sub(Nat.sub(max, 1n), done)

def rounds.text(left: Nat, +max: Nat) -> String:
  match left:
    case 0n:
      String.concat(["Harness note: no tool round remains in this turn (maxToolRounds ", Nat.show(max), "): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."])
    case 1n:
      String.concat(["Harness note: 1 tool round remains in this turn (maxToolRounds ", Nat.show(max), "). Use it for the remaining work; if the work cannot finish in it, end with a final answer that states what is done and exactly what remains."])
    case 2n+p:
      String.concat(["Harness note: ", Nat.show(2n+p), " tool rounds remain in this turn (maxToolRounds ", Nat.show(max), "). Use them for the remaining work; if the work cannot finish in them, end with a final answer that states what is done and exactly what remains."])

def rounds.at(near: Bool, +left: Nat, +max: Nat) -> Maybe<&2, String>:
  match near:
    case True{}:
      Some{rounds.text(left, max)}
    case False{}:
      None{}

# the note that ends a request after `done` tool rounds of `max`: the
# rounds left once they are at most low(), else none
def rounds(+max: Nat, +done: Nat) -> Maybe<&2, String>:
  +l = left(max, done)
  rounds.at(Nat.is_le(l, low()), l, max)
