# launcher: the model of a daemon replacement (docs/daemon.md D1): the
# idle shutdown and the adoption of live workers. The Rust code is
# crates/eukhe-daemon/src/work_gate.rs (`WorkGate`, `idle_shutdown_commits`)
# and `supervisor/adoption.rs` `adoption_verdict`; the bridge
# (bend/bridge_launcher.bend, crates/eukhe-daemon/src/supervision_bridge.rs)
# runs both on the same operations.
#
# The idle shutdown: any operations, in any order, on any workers. A
# prompt starts a run on a worker whose gate is open (a closed gate refuses
# it); a run ends; the supervisor quiesces a worker (an idle worker closes
# its gate, a busy one answers busy and stays open) or releases it (its
# gate opens); the supervisor commits the shutdown, which stops every
# worker only when every gate is closed (each answer was "quiesced").
# Every run a stop finds is aborted.

import Base

type Op is Data:
  Prompt{i: Nat}
  Finish{i: Nat}
  Quiesce{i: Nat}
  Release{i: Nat}
  Commit{}

# a worker: its run, its gate (True: closed by a quiesce)
type Wk is Data:
  Wk{busy: Bool, closed: Bool}

# the workers, the runs a stop aborted, whether the daemon stopped
type St is Data:
  St{ws: List<&2, Wk>, aborted: Nat, stopped: Bool}

def St.aborted(s: St) -> Nat:
  match s:
    case St{ws, a, d}:
      a

def prompt(w: Wk) -> Wk:
  match w:
    case Wk{b, c}:
      match c:
        case True{}:
          Wk{b, True{}}
        case False{}:
          Wk{True{}, False{}}

def finish(w: Wk) -> Wk:
  match w:
    case Wk{b, c}:
      Wk{False{}, c}

def quiesce(w: Wk) -> Wk:
  match w:
    case Wk{b, c}:
      match b:
        case True{}:
          Wk{True{}, c}
        case False{}:
          Wk{False{}, True{}}

def release(w: Wk) -> Wk:
  match w:
    case Wk{b, c}:
      Wk{b, False{}}

# apply f to worker i
def at(~f: Wk -> Wk, i: Nat, ws: List<&2, Wk>) -> List<&2, Wk>:
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Nil{}
        case w <> t:
          f(w) <> t
    case 1n+j:
      match ws:
        case Nil{}:
          Nil{}
        case w <> t:
          w <> at(~f, j, t)

def all_closed(ws: List<&2, Wk>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case w <> t:
      match w:
        case Wk{b, c}:
          Bool.and(c, all_closed(t))

def busy_count(ws: List<&2, Wk>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case w <> t:
      match w:
        case Wk{b, c}:
          match b:
            case True{}:
              1n+busy_count(t)
            case False{}:
              busy_count(t)

def commit.put(ok: Bool, +ws: List<&2, Wk>, a: Nat) -> St:
  match ok:
    case True{}:
      St{ws, Nat.add(busy_count(ws), a), True{}}
    case False{}:
      St{ws, a, False{}}

def step(s: St, op: Op) -> St:
  match s:
    case St{+ws, a, d}:
      match d:
        case True{}:
          St{ws, a, True{}}
        case False{}:
          match op:
            case Prompt{i}:
              St{at(~prompt, i, ws), a, False{}}
            case Finish{i}:
              St{at(~finish, i, ws), a, False{}}
            case Quiesce{i}:
              St{at(~quiesce, i, ws), a, False{}}
            case Release{i}:
              St{at(~release, i, ws), a, False{}}
            case Commit{}:
              commit.put(all_closed(ws), ws, a)

def go(ops: List<&2, Op>, s: St) -> St:
  match ops:
    case Nil{}:
      s
    case op <> rest:
      go(rest, step(s, op))

# workers with these runs and open gates
def open(bs: List<&2, Bool>) -> List<&2, Wk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      Wk{b, False{}} <> open(t)

def run(bs: List<&2, Bool>, ops: List<&2, Op>) -> St:
  go(ops, St{open(bs), 0n, False{}})

# Adoption
# --------
# A build is a number (the bridge numbers the build ids). A worker reports
# its build, or none.

type Adoption is Data:
  Adopt{}
  Replace{}

def adopt.put(same: Bool) -> Adoption:
  match same:
    case True{}:
      Adopt{}
    case False{}:
      Replace{}

def adoption(+sup: Nat, w: Maybe<&2, Nat>) -> Adoption:
  match w:
    case None{}:
      Replace{}
    case Some{b}:
      adopt.put(Nat.is_eq(b, sup))
