# memory (spec): what the laws of area thread (laws/thread.bend) speak of,
# over the model in bend/thread.bend: each session is its own thread. The
# terms check a request or a count (whose messages, which starts, which
# lines over which spans); none of them builds a request or counts lines.
# A spec: the shipped code never calls it. The proofs in proof/thread/ use
# it too.
#
# S1: the chat of a session is the messages of the event stream that it
#     wrote, in order, and nothing else.
# S2: a request belongs to its session: every turn it carries, and every
#     message a view line of it summarizes, was written by that session.
# S3: the newest turns are verbatim: the request ends with the turns of
#     the chat's newest messages, in order, unchanged, after every view
#     line; the chat's messages before them are exactly end = T - V (T the
#     messages the chat holds, V the window the transcript holds, 0 when V
#     passes T).
# S4: the view keeps only the history that scrolled out: every view line
#     of the request starts before end; over a view whose lines ascend, the
#     request holds exactly the view lines that start before end, in order.
# S5: the count of kept lines is the length of the longest run of leading
#     starts below end.
# S6: the request, whole: the leading view lines that start before end,
#     each with the count messages of the chat from its own start, then
#     the turns of the chat's messages from end on.

import Base
import ../../bend/thread.bend as Th

# Chats (S1)
# ----------

# session s wrote m
def mine(+s: Nat, m: Th.Msg) -> Bool:
  match m:
    case Th.Msg{who, body}:
      Nat.is_eq(who, s)

def only(b: Bool, m: Th.Msg) -> List<&2, Th.Msg>:
  match b:
    case True{}:
      [m]
    case False{}:
      []

# the chat of session s: each message of evs that s wrote, in order
def chat(+s: Nat, evs: List<&2, Th.Msg>) -> List<&2, Th.Msg>:
  match evs:
    case Nil{}:
      Nil{}
    case +m <> t:
      List.append(&2, Th.Msg, only(mine(s, m), m), chat(s, t))

# Ownership (S2)
# --------------

# session s wrote every message of ms
def own(+s: Nat, ms: List<&2, Th.Msg>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(mine(s, m), own(s, t))

def item_own(+s: Nat, it: Th.Item) -> Bool:
  match it:
    case Th.Line{st, ms}:
      own(s, ms)
    case Th.Turn{m}:
      mine(s, m)

# session s wrote every turn of its, and every message a line of its covers
def items_own(+s: Nat, its: List<&2, Th.Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case it <> t:
      Bool.and(item_own(s, it), items_own(s, t))

# Verbatim turns (S3)
# -------------------

# each message, as a turn
def turns(ms: List<&2, Th.Msg>) -> List<&2, Th.Item>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> t:
      Th.Turn{m} <> turns(t)

def is_line(it: Th.Item) -> Bool:
  match it:
    case Th.Line{st, ms}:
      True{}
    case Th.Turn{m}:
      False{}

# its holds no turn: view lines only
def no_turns(its: List<&2, Th.Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case it <> t:
      Bool.and(is_line(it), no_turns(t))

# History (S4, S5)
# ----------------

# end = T - V: the messages of the chat the transcript no longer holds
def end(+ch: List<&2, Th.Msg>, window: Nat) -> Nat:
  Nat.sub(List.length(&2, Th.Msg, ch), window)

def item_before(+e: Nat, it: Th.Item) -> Bool:
  match it:
    case Th.Line{st, ms}:
      Nat.is_lt(st, e)
    case Th.Turn{m}:
      True{}

# every view line of its starts before e
def lines_before(+e: Nat, its: List<&2, Th.Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case it <> t:
      Bool.and(item_before(e, it), lines_before(e, t))

def item_start(it: Th.Item) -> List<&2, Nat>:
  match it:
    case Th.Line{st, ms}:
      [st]
    case Th.Turn{m}:
      []

# the first message of each view line of its, in order
def line_starts(its: List<&2, Th.Item>) -> List<&2, Nat>:
  match its:
    case Nil{}:
      Nil{}
    case it <> t:
      List.append(&2, Nat, item_start(it), line_starts(t))

# the first message of each line of a view, in order
def view_starts(view: List<&2, Th.Span>) -> List<&2, Nat>:
  match view:
    case Nil{}:
      Nil{}
    case sp <> t:
      match sp:
        case Th.Span{st, c}:
          st <> view_starts(t)

def below(b: Bool, x: Nat) -> List<&2, Nat>:
  match b:
    case True{}:
      [x]
    case False{}:
      []

# the items of xs below e, in order
def before(+e: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      List.append(&2, Nat, below(Nat.is_lt(x, e), x), before(e, t))

def ascending.go(xs: List<&2, Nat>, +prev: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.and(Nat.is_le(prev, x), ascending.go(t, x))

# each item of xs is at most the next
def ascending(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      ascending.go(t, x)

# every item of xs is below e
def all_below(+e: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(Nat.is_lt(x, e), all_below(e, t))

# xs is empty or opens with an item at e or past it
def opens_at_or_past(e: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_le(e, x)

# S5: n is the length of the leading run of xs below e: at most the
# length of xs, the first n items below e, and the next one (if any) not
def leading(+e: Nat, +xs: List<&2, Nat>, +n: Nat) -> Bool:
  Bool.and(Nat.is_le(n, List.length(&2, Nat, xs)), Bool.and(all_below(e, List.take(&2, Nat, xs, n)), opens_at_or_past(e, List.drop(&2, Nat, xs, n))))

# The request (S6)
# ----------------

def msg_eq(a: Th.Msg, b: Th.Msg) -> Bool:
  match a:
    case Th.Msg{s1, b1}:
      match b:
        case Th.Msg{s2, b2}:
          Bool.and(Nat.is_eq(s1, s2), Nat.is_eq(b1, b2))

# ms opens d: each message of ms is the message of d at its place
def is_prefix(ms: List<&2, Th.Msg>, d: List<&2, Th.Msg>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> mt:
      match d:
        case Nil{}:
          False{}
        case x <> dt:
          Bool.and(msg_eq(m, x), is_prefix(mt, dt))

# ms is the first c messages of d, or all of d when d holds fewer
def covers(+ms: List<&2, Th.Msg>, +d: List<&2, Th.Msg>, +c: Nat) -> Bool:
  Bool.and(is_prefix(ms, d), Nat.is_eq(List.length(&2, Th.Msg, ms), Nat.min(c, List.length(&2, Th.Msg, d))))

def span_start(sp: Th.Span) -> Nat:
  match sp:
    case Th.Span{st, c}:
      st

# it is the view line of span sp over the chat ch: a line at sp's start
# that covers the chat's messages from that start on (count of them)
def line_ok(+ch: List<&2, Th.Msg>, sp: Th.Span, it: Th.Item) -> Bool:
  match sp:
    case Th.Span{+st, c}:
      match it:
        case Th.Line{st2, ms}:
          Bool.and(Nat.is_eq(st2, st), covers(ms, List.drop(&2, Th.Msg, ch, st), c))
        case Th.Turn{m}:
          False{}

def is_turn(it: Th.Item) -> Bool:
  match it:
    case Th.Line{st, ms}:
      False{}
    case Th.Turn{m}:
      True{}

# its holds no view line
def no_lines(its: List<&2, Th.Item>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case it <> t:
      Bool.and(is_turn(it), no_lines(t))

def sel(b: Bool, x: Bool, y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

# S6: the view lines of its, in order, are one line per leading span of
# view that starts before e, each the line of its span over the chat ch
# (line_ok); after them its holds no view line
def lines_match(view: List<&2, Th.Span>, +ch: List<&2, Th.Msg>, +e: Nat, its: List<&2, Th.Item>) -> Bool:
  match view:
    case Nil{}:
      no_lines(its)
    case +sp <> vt:
      match its:
        case Nil{}:
          Nat.is_le(e, span_start(sp))
        case +it <> +rest:
          sel(Nat.is_lt(span_start(sp), e), Bool.and(line_ok(ch, sp, it), lines_match(vt, ch, e, rest)), no_lines(it <> rest))
