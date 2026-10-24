# tiny: the model of the local tiny-model service (docs/inference.md, S9),
# after omp's local models. A role (titles, classification, translation,
# speech, dictation) names a chain of models, local or remote. A task goes
# to the first model of the chain that is available; with none available
# it fails as Unavailable, never on a model outside the chain.
#
# A local model runs in one worker process per model, shared by every
# eukhe process. A process that needs the model connects to the worker;
# with no worker it tries to take the bind lock and starts one. A worker
# answers ping with its tag (build and settings); a process whose tag
# differs replaces the worker. An idle worker exits.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# 1. The chain
# ------------

type Pick is Data:
  Use{model: Nat}
  Unavailable{}

# the head of chain is in up
def up.at(+chain: List<&2, Nat>, +up: List<&2, Nat>) -> Bool:
  match chain:
    case Nil{}:
      False{}
    case m <> rest:
      elem(up, m)

# the first model of chain that `up` holds; hit is elem(up, head)
def pick.go(chain: List<&2, Nat>, +up: List<&2, Nat>, hit: Bool) -> Pick:
  match chain:
    case Nil{}:
      Unavailable{}
    case +m <> +rest:
      match hit:
        case True{}:
          Use{m}
        case False{}:
          pick.go(rest, up, up.at(rest, up))

def pick(+chain: List<&2, Nat>, +up: List<&2, Nat>) -> Pick:
  pick.go(chain, up, up.at(chain, up))

# no model of xs is in up
def none_up(xs: List<&2, Nat>, +up: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.not(elem(up, x)), none_up(rest, up))

# 2. The worker of one model
# --------------------------

type Ev is Data:
  Need{p: Nat, tag: Nat}  # process p needs the model, with its tag
  Gone{}                  # the worker exits (idle, crash, replaced)

# the worker: none, or running with its owner process and tag
type W is Data:
  NoWorker{}
  Worker{owner: Nat, tag: Nat}

# What a need ends in
type Got is Data:
  Started{}    # the process took the lock and started the worker
  Joined{}     # the process connected to a worker with its tag
  Replaced{}   # the worker had another tag: the process replaced it

def W.tag(w: W) -> Maybe<&2, Nat>:
  match w:
    case NoWorker{}:
      None{}
    case Worker{o, t}:
      Some{t}

# the worker after a need of process p with tag, when a worker with tag
# t runs: same tag joins it, another tag replaces it
def need.w(same: Bool, +p: Nat, +tag: Nat, w: W) -> W:
  match same:
    case True{}:
      w
    case False{}:
      Worker{p, tag}

def need.g(same: Bool) -> Got:
  match same:
    case True{}:
      Joined{}
    case False{}:
      Replaced{}

# the worker after one event
def step(w: W, e: Ev) -> W:
  match w:
    case NoWorker{}:
      match e:
        case Gone{}:
          NoWorker{}
        case Need{p, tag}:
          Worker{p, tag}
    case Worker{o, +t}:
      match e:
        case Gone{}:
          NoWorker{}
        case Need{+p, +tag}:
          need.w(Nat.is_eq(t, tag), p, tag, Worker{o, t})

# what one event's need got (none for an exit)
def got(w: W, e: Ev) -> List<&2, Got>:
  match w:
    case NoWorker{}:
      match e:
        case Gone{}:
          Nil{}
        case Need{p, tag}:
          [Started{}]
    case Worker{o, t}:
      match e:
        case Gone{}:
          Nil{}
        case Need{p, tag}:
          [need.g(Nat.is_eq(t, tag))]

# the worker after events
def run(es: List<&2, Ev>, w: W) -> W:
  match es:
    case Nil{}:
      w
    case e <> rest:
      run(rest, step(w, e))

# what each need got, in order
def gots(es: List<&2, Ev>, +w: W) -> List<&2, Got>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, Got, got(w, e), gots(rest, step(w, e)))

# the tag of the last need among es, if any
def last_tag(es: List<&2, Ev>, t: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      t
    case e <> rest:
      match e:
        case Need{p, tag}:
          last_tag(rest, Some{tag})
        case Gone{}:
          last_tag(rest, None{})

# the number of needs among es
def needs(es: List<&2, Ev>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Need{p, t}:
          1n+needs(rest)
        case Gone{}:
          needs(rest)

# 3. One process's election
# -------------------------
# The worker of section 2 as one process meets it (crates/eukhe-tiny
# election.rs): the process pings the worker's socket and decides from
# what answers alone (it never sees the owner). Rust connects, pings,
# shuts down, launches and reports; each choice below runs as the
# compiled core (bend/ffi_tiny_elect.bend).

# what a ping of the worker's socket met
type Probe is Data:
  Missing{}          # no socket, or a refused one: no worker
  Unreachable{}      # the connect failed otherwise
  Pong{tag: String}  # a worker answered with its launch tag
  Odd{}              # a worker answered the ping with another reply
  Garbled{}          # the answer is no line of the protocol
  Hung{}             # the connection closed or failed on the ping

# what the process does after its first ping
type Act is Data:
  Join{}     # a live worker has its tag: use it
  Replace{}  # a live worker has another tag: shut it down, start one
  Start{}    # no live worker: start one
  Broken{}   # the socket failed or spoke out of protocol: an IO error

# a and b are the same text, char by char
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(x, y), same(u, v))

def elect.pong(s: Bool) -> Act:
  match s:
    case True{}:
      Join{}
    case False{}:
      Replace{}

# the first choice of a process with launch tag mine
def elect(p: Probe, mine: String) -> Act:
  match p:
    case Missing{}:
      Start{}
    case Unreachable{}:
      Broken{}
    case Pong{t}:
      elect.pong(same(t, mine))
    case Odd{}:
      Broken{}
    case Garbled{}:
      Broken{}
    case Hung{}:
      Start{}

# what the shutdown of a worker of another tag heard
type Heard is Data:
  Bye{}    # the worker said bye
  Other{}  # it answered with something else
  Eof{}    # it closed first: it exited on its own meanwhile
  Lost{}   # the connection failed otherwise

type Shut is Data:
  Down{}   # the worker is gone: start one
  Spoke{}  # out of protocol
  Cut{}    # an IO error

def shut(h: Heard) -> Shut:
  match h:
    case Bye{}:
      Down{}
    case Other{}:
      Spoke{}
    case Eof{}:
      Down{}
    case Lost{}:
      Cut{}

# a start the process made: of a first worker, or of a replacement
type Fresh is Data:
  First{}
  Again{}

# how a started worker came up
type Launch is Data:
  Bound{}    # it bound the socket and serves
  Adopted{}  # another worker took the socket first; the started one left

# what a need that started a worker got
def launched(f: Fresh, l: Launch) -> Got:
  match f:
    case First{}:
      match l:
        case Bound{}:
          Started{}
        case Adopted{}:
          Joined{}
    case Again{}:
      match l:
        case Bound{}:
          Replaced{}
        case Adopted{}:
          Joined{}

# what the ping after a start met, for the process
type Check is Data:
  Serving{}    # a worker with its tag answers: use it
  Mistagged{}  # a worker of another tag answers: the start failed
  Vacant{}     # no worker answers: the start failed
  Faulty{}     # the socket failed or spoke out of protocol: an IO error

def confirm.pong(s: Bool) -> Check:
  match s:
    case True{}:
      Serving{}
    case False{}:
      Mistagged{}

# the check after a start, of a process with launch tag mine
def confirm(p: Probe, mine: String) -> Check:
  match p:
    case Missing{}:
      Vacant{}
    case Unreachable{}:
      Faulty{}
    case Pong{t}:
      confirm.pong(same(t, mine))
    case Odd{}:
      Faulty{}
    case Garbled{}:
      Faulty{}
    case Hung{}:
      Vacant{}

# what a started worker does with the socket (crates/eukhe-tiny
# worker.rs `bind`), after its own ping of it
type Seat is Data:
  Adopt{}  # a live worker answers (any tag): leave it in place and exit
  Take{}   # no live worker: remove a stale socket and bind it
  Fault{}  # the socket failed or spoke out of protocol: an IO error

def bind(p: Probe) -> Seat:
  match p:
    case Missing{}:
      Take{}
    case Unreachable{}:
      Fault{}
    case Pong{t}:
      Adopt{}
    case Odd{}:
      Fault{}
    case Garbled{}:
      Fault{}
    case Hung{}:
      Take{}
