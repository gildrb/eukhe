# notice: the model of the kernel restore notices a TUI view shows
# (docs/daemon.md D1). The Rust code is
# crates/eukhe-tui/src/restore_notices.rs (`RestoreNotices`); the bridge
# (bend/bridge_notice.bend, `the_restore_notices_run_as_their_model` in
# that file) runs both on the same events.
#
# A kernel restore stores one notice in the session. The newest notice
# can arrive as a live event. An attach (a reconnect, a worker restart)
# rebuilds the transcript from every stored notice. Each notice shows
# when the view's record does not hold it, and a notice that shows joins
# the record. The state is the stored notices in order: for each one,
# whether the record holds it and how many times it showed.

import Base

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
