# thread: each session is its own thread (Rust: eukhe-core
# memory/service.rs RenderedView::history, durable/optchat/request.rs pin).
# A session logs only its own messages into its own chat
# (<agent-dir>/chat/sessions/<session>/), so its view (summary lines over
# that log, oldest first) holds only its own messages. A root turn's
# request is the view lines of the history that scrolled out of the
# verbatim transcript, then the session's own transcript verbatim (the
# newest `window` messages of its chat). Of the view lines, the request
# keeps exactly the leading ones that start before end = T - V (T the
# messages the chat holds, V the ones the transcript still holds; 0 when V
# passes T); a line that straddles end stays whole. A call sends the view
# pinned under the transcript's head (its newest compaction or reset) and
# renders a fresh one only under a new head, so between two compactions
# the request only grows at its end. Pure: no IO, no @unsafe.

import Base

# one message of the event stream: the session that wrote it, its body
type Msg is Data:
  Msg{session: Nat, body: Nat}

# a line of a session's view: the first message of its chat it covers,
# and how many
type Span is Data:
  Span{start: Nat, count: Nat}

# one entry of a request: a view line (its first message and the messages
# it summarizes) or a turn of the transcript, verbatim
type Item is Data:
  Line{start: Nat, covers: List<&2, Msg>}
  Turn{msg: Msg}

# a root's pinned view (Rust: CallState): the head of the transcript it
# was rendered under (the newest compaction or reset entry; 0 before the
# first, as entry ids start at 1) and its lines
type Pin is Data:
  Pin{head: Nat, view: List<&2, Span>}

# Chats
# -----

def log.keep(b: Bool, m: Msg, rest: List<&2, Msg>) -> List<&2, Msg>:
  match b:
    case True{}:
      m <> rest
    case False{}:
      rest

def log.one(+s: Nat, m: Msg, rest: List<&2, Msg>) -> List<&2, Msg>:
  match m:
    case Msg{+who, body}:
      log.keep(Nat.is_eq(who, s), Msg{who, body}, rest)

# the chat of session s: the messages of the stream evs that s wrote, in
# order
def log(+s: Nat, evs: List<&2, Msg>) -> List<&2, Msg>:
  match evs:
    case Nil{}:
      Nil{}
    case m <> t:
      log.one(s, m, log(s, t))

# History
# -------

def Span.start(sp: Span) -> Nat:
  match sp:
    case Span{st, c}:
      st

# the first message of each line of a view, in order
def starts(view: List<&2, Span>) -> List<&2, Nat>:
  match view:
    case Nil{}:
      Nil{}
    case sp <> t:
      Span.start(sp) <> starts(t)

def history_lines.step(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      0n

def history_lines.go(xs: List<&2, Nat>, +end: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      history_lines.step(Nat.is_lt(x, end), history_lines.go(t, end))

# how many leading view lines (their first messages `starts`, oldest
# first) a request keeps: those that start before end = through -
# verbatim (0 when verbatim passes through)
def history_lines(through: Nat, verbatim: Nat, starts: List<&2, Nat>) -> Nat:
  history_lines.go(starts, Nat.sub(through, verbatim))

# Requests
# --------

# a view line over the chat lg: the messages it covers
def line(+lg: List<&2, Msg>, sp: Span) -> Item:
  match sp:
    case Span{+st, c}:
      Line{st, List.take(&2, Msg, List.drop(&2, Msg, lg, st), c)}

def lines(+lg: List<&2, Msg>, view: List<&2, Span>) -> List<&2, Item>:
  match view:
    case Nil{}:
      Nil{}
    case sp <> t:
      line(lg, sp) <> lines(lg, t)

def turns(ms: List<&2, Msg>) -> List<&2, Item>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> t:
      Turn{m} <> turns(t)

# the request of a root turn of session s, over the stream evs, its view
# and the `window` newest messages its transcript holds: the kept view
# lines, then the transcript verbatim
def request(+s: Nat, evs: List<&2, Msg>, +view: List<&2, Span>, +window: Nat) -> List<&2, Item>:
  +lg = log(s, evs)
  +total = List.length(&2, Msg, lg)
  +kept = List.take(&2, Span, view, history_lines(total, window, starts(view)))
  List.append(&2, Item, lines(lg, kept), turns(List.drop(&2, Msg, lg, Nat.sub(total, window))))

# Pins
# ----

def pin.keep(b: Bool, p: Pin, +head: Nat, fresh: List<&2, Span>) -> Pin:
  match b:
    case True{}:
      p
    case False{}:
      Pin{head, fresh}

# the pin a call sends (Rust: request.rs transform): the pinned view while
# the transcript keeps the head it was rendered under, else the fresh
# render, pinned under the transcript's new head
def pin(p: Pin, +head: Nat, fresh: List<&2, Span>) -> Pin:
  match p:
    case Pin{+h, v}:
      pin.keep(Nat.is_eq(h, head), Pin{h, v}, head, fresh)
