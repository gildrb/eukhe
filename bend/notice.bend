# notice: the kernel restore notices a TUI view shows (docs/daemon.md D1).
# The rule below runs compiled (bend/ffi_notice.bend, a stepper) under
# crates/eukhe-tui/src/restore_notices.rs (`RestoreNotices`): Rust sends
# each message it asks about and each batch of messages it shows; this
# file decides. Pure: no IO, no @unsafe.
#
# A worker that boots a kernel over a namespace snapshot stores one
# restore notice in the session: a custom message of kind
# ipython_state_restored, stamped with the time it was stored (the same
# stamp in every transcript and every live event of the session). Each
# attach (a reconnect, a worker restart, a session rebind) and each
# transcript refetch rebuilds the transcript from every stored message.
# The view's record holds the session id and the stamp of each restore
# notice it showed. A message shows unless it is a restore notice whose
# session and stamp the record holds; the messages the view shows join
# the record. Ids and stamps are text (Rust sends a u64 stamp as its
# decimal digits): the rule only compares them, char by char.

import Base

# The rule
# --------

# A message as the rule reads it: a custom message (its kind and its
# stamp), or a message of any other role.
type Msg is Data:
  Other{}
  Custom{kind: String, stamp: String}

# A restore notice the view showed: its session id and its stamp.
type Seen is Data:
  Seen{sid: String, stamp: String}

# What the view asks: whether a message of a session shows, or to record
# the messages of a session it shows now.
type Ask is Data:
  Shows{sid: String, m: Msg}
  Notes{sid: String, ms: List<&2, Msg>}

# The answer to an ask.
type Ans is Data:
  Shown{b: Bool}
  Noted{}

# The kind of a restore notice (eukhe-types `CustomType::IpythonStateRestored`).
def restore_kind() -> String:
  "ipython_state_restored"

# a and b hold the same chars, in the same order
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{d, u}:
      False{}
    case SCon{c, t} SNil{}:
      False{}
    case SCon{c, t} SCon{d, u}:
      Bool.and(Char.is_eq(c, d), same(t, u))

def notice.of(hit: Bool, s: String) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{s}
    case False{}:
      None{}

# the stamp of m when m is a restore notice
def notice(m: Msg) -> Maybe<&2, String>:
  match m:
    case Other{}:
      None{}
    case Custom{k, s}:
      notice.of(same(k, restore_kind()), s)

# the record holds the notice of session sid stamped s
def held(rs: List<&2, Seen>, +sid: String, +s: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case Seen{a, b}:
          Bool.or(Bool.and(same(a, sid), same(b, s)), held(t, sid, s))

def visible.at(rs: List<&2, Seen>, +sid: String, n: Maybe<&2, String>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{s}:
      Bool.not(held(rs, sid, s))

# the decision: m of session sid shows unless it is a restore notice the
# record holds
def visible(rs: List<&2, Seen>, +sid: String, m: Msg) -> Bool:
  visible.at(rs, sid, notice(m))

def record.one(n: Maybe<&2, String>, +sid: String, rs: List<&2, Seen>) -> List<&2, Seen>:
  match n:
    case None{}:
      rs
    case Some{s}:
      Seen{sid, s} <> rs

def record.go(ms: List<&2, Msg>, +sid: String, rs: List<&2, Seen>) -> List<&2, Seen>:
  match ms:
    case Nil{}:
      rs
    case m <> t:
      record.go(t, sid, record.one(notice(m), sid, rs))

# the record after the view shows the messages ms of session sid: each
# restore notice among them joins it
def record(rs: List<&2, Seen>, +sid: String, ms: List<&2, Msg>) -> List<&2, Seen>:
  record.go(ms, sid, rs)

# one ask: a question keeps the record; a record of shown messages
# answers nothing
def answer(+rs: List<&2, Seen>, q: Ask) -> List<&2, Seen> & Ans:
  match q:
    case Shows{sid, m}:
      (rs, Shown{visible(rs, sid, m)})
    case Notes{sid, ms}:
      (record(rs, sid, ms), Noted{})

# The model of the scenario
# -------------------------
#
# The rule above, abstracted to positions: a kernel restore stores one
# notice in the session. The newest notice can arrive as a live event. An
# attach (a reconnect, a worker restart) rebuilds the transcript from
# every stored notice. Each notice shows when the view's record does not
# hold it, and a notice that shows joins the record. The state is the
# stored notices in order: for each one, whether the record holds it and
# how many times it showed. laws/notice.bend (notice_real_refines) ties
# the rule to this model.

type N is Data:
  N{seen: Bool, shown: Nat}

type Ev is Data:
  Restore{}
  Live{}
  Reconnect{}

# the decision: a notice shows when the record does not hold it
def shows(seen: Bool) -> Bool:
  Bool.not(seen)

def show.put(b: Bool, s: Bool, c: Nat) -> N:
  match b:
    case True{}:
      N{True{}, 1n+c}
    case False{}:
      N{s, c}

# a notice offered to the view
def show(n: N) -> N:
  match n:
    case N{+s, c}:
      show.put(shows(s), s, c)

# an attach: every stored notice is offered
def rebuild(ns: List<&2, N>) -> List<&2, N>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      show(n) <> rebuild(t)

# the newest notice (the last of t, else n) arrives live
def live.at(t: List<&2, N>, n: N) -> List<&2, N>:
  match t:
    case Nil{}:
      show(n) <> Nil{}
    case m <> u:
      n <> live.at(u, m)

def live(ns: List<&2, N>) -> List<&2, N>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      live.at(t, n)

def step(ns: List<&2, N>, e: Ev) -> List<&2, N>:
  match e:
    case Restore{}:
      List.append(&2, N, ns, [N{False{}, 0n}])
    case Live{}:
      live(ns)
    case Reconnect{}:
      rebuild(ns)

def go(evs: List<&2, Ev>, ns: List<&2, N>) -> List<&2, N>:
  match evs:
    case Nil{}:
      ns
    case e <> rest:
      go(rest, step(ns, e))

# the stored notices after the events, from a view that showed nothing
def run(evs: List<&2, Ev>) -> List<&2, N>:
  go(evs, Nil{})

# the restores among the events
def restores(evs: List<&2, Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Restore{}:
          1n+restores(rest)
        case Live{}:
          restores(rest)
        case Reconnect{}:
          restores(rest)

# the restore rows the view showed in all
def total(ns: List<&2, N>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> t:
      match n:
        case N{s, c}:
          Nat.add(c, total(t))

def at_most_one(c: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          False{}

# every stored notice showed at most once
def once(ns: List<&2, N>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> t:
      match n:
        case N{s, c}:
          Bool.and(at_most_one(c), once(t))
