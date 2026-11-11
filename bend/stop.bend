# stop: the Directors at a candidate stop of the run loop (the Rust host
# is crates/eukhe-durable/src/harness/generation/stop.rs; laws/stop.bend
# states the laws, spec/harness/stop.bend the spec they refine). A
# candidate stop is a model reply that ends the model's turn with no tool
# call. As omp2's Directors (ADR 0015), the run walks a stack of Directors
# at it, inside to outside; each gives a verdict:
#
# - Pass: the next Director decides;
# - Continue: the run goes on, with the Director's reminder at the end of
#   the next request (a harness note, never logged as the user's words),
#   or, at a length stop whose window ran out, after a compaction;
#   bend/run/recovery.bend counts each Director's reminders in a row and
#   stops it at its cap;
# - Yield: the stop stands.
#
# With every Director passing, the stop stands: the reply is the final
# answer, whatever its text says. The Directors, inside to outside:
#
# - LengthStop: the reply hit the output limit. With no text nothing was
#   delivered, and with the window run out (full) the next request needs a
#   compaction: the run goes on. A cut reply with text and room left in
#   the window is kept as it is (omp keeps a truncated turn that delivered
#   text): the stop stands, whatever else the text holds;
# - EmptyStop: no text: nothing the user can read (a thinking-only reply);
# - MarkupStop: tool-call markup in the text that the harness could not
#   read: a call the model meant to make, never an answer;
# - PendingWork: the session owns running work (jobs, children, workflow
#   runs): the stop is a pause, their ends wake the session.
#
# Pure: no IO, no @unsafe.

import Base

# The facts of a candidate stop
# -----------------------------

# cut: the reply hit the output limit (stop reason length); text: a text
# block that is not blank; broken: tool-call markup in the text that the
# harness could not read; pending: the session owns running work; full:
# the window is what ran out at a cut reply and a compaction can run
# (bend/run/recovery.bend `full`), so a compaction makes room for the
# reply's request
type Facts is Data:
  Facts{cut: Bool, text: Bool, broken: Bool, pending: Bool, full: Bool}

# The Directors
type Dir is Data:
  LengthStop{}
  EmptyStop{}
  MarkupStop{}
  PendingWork{}

type Verdict is Data:
  Pass{}
  Continue{}
  Yield{}

# what the walk picks: the stop stands, or the Director d continues the run
type Pick is Data:
  Stands{}
  Goes{d: Dir}

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
    case Facts{cut, text, broken, pending, full}:
      cut

def Facts.text(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, full}:
      text

def Facts.broken(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, full}:
      broken

def Facts.pending(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, full}:
      pending

def Facts.full(f: Facts) -> Bool:
  match f:
    case Facts{cut, text, broken, pending, full}:
      full

# LengthStop at a cut reply: it stands when it has text and the window has
# room; else the run goes on
def cut.at(text: Bool, full: Bool) -> Verdict:
  match text:
    case True{}:
      match full:
        case True{}:
          Continue{}
        case False{}:
          Yield{}
    case False{}:
      Continue{}

# LengthStop: only a cut reply is its to decide
def length(cut: Bool, text: Bool, full: Bool) -> Verdict:
  match cut:
    case True{}:
      cut.at(text, full)
    case False{}:
      Pass{}

# the verdict of the Director d at the stop f
def verdict(d: Dir, +f: Facts) -> Verdict:
  match d:
    case LengthStop{}:
      length(Facts.cut(f), Facts.text(f), Facts.full(f))
    case EmptyStop{}:
      on(Bool.not(Facts.text(f)))
    case MarkupStop{}:
      on(Facts.broken(f))
    case PendingWork{}:
      hold(Facts.pending(f))

# the stack, inside to outside
def stack() -> List<&2, Dir>:
  [LengthStop{}, EmptyStop{}, MarkupStop{}, PendingWork{}]

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

# the reminders in a row of EmptyStop (omp EMPTY_STOP_MAX_RETRIES);
# LengthStop and MarkupStop keep the caps of their recoveries
# (LENGTH_NOTES of the ladder of bend/run/recovery.bend, LEAK_NOTES)
def empty_cap() -> Nat:
  3n

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
