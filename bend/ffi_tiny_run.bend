# ffi_tiny_run: the stepper of the compiled Bend core for one process's
# election of a tiny model's worker, and for a started worker's seat
# (bend/tiny.bend section 4; Rust: crates/eukhe-tiny/src/election.rs,
# worker.rs `bind`). Its state is the model's run, kept in the Bend heap.
# Rust sends each outcome of what it was told to do, in the order they
# arrive; the reply is what it does next. The codec is the wire format of
# bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    0, mine: String (a need, the process's launch tag)
#           | 1 (a started worker's seat)               reply: Do
#   step    Seen                                        reply: Do
#
#   Seen    0, Probe (a ping met it) | 1, Heard (a shutdown's answer)
#           | 2, Launch (a launch ended) | 3 (a launch failed)
#           | 4 (the bind lock is held)
#   Probe   0 Missing | 1 Unreachable | 2 Pong{tag: String} | 3 Odd
#           | 4 Garbled | 5 Hung
#   Heard   0 Bye | 1 Other | 2 Eof | 3 Lost
#   Launch  0 Bound | 1 Adopted
#   Do      0 Ping | 1 Shutdown | 2 Launch | 3 Use, Got | 4 Fail, Why
#           | 5 Lock | 6 Adopt | 7 Take | 8 Fault | 9 Nothing
#   Got     0 Started | 1 Joined | 2 Replaced
#   Why     0 Io | 1 Protocol | 2 Mistagged | 3 Vacant | 4 Spawn
#
# A malformed open (or one with input left over) opens the refused state
# and answers `E tiny_run: malformed open`; the refused state answers
# every step `E tiny_run: the open was refused`. A malformed event (or
# one with input left over) keeps the run and answers
# `E tiny_run: malformed event`. laws/tiny.bend (tiny_run_entry_*) pins
# the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./tiny.bend as Tn

# Decoders
# --------

def get_probe.pong(r: W.Dec<String>) -> W.Dec<Tn.Probe>:
  match r:
    case W.Got{t, s}:
      W.Got{Tn.Pong{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_probe.tag(t: Nat, s: String) -> W.Dec<Tn.Probe>:
  match t:
    case 0n:
      W.Got{Tn.Missing{}, s}
    case 1n:
      W.Got{Tn.Unreachable{}, s}
    case 2n:
      get_probe.pong(W.get_str(s))
    case 3n:
      W.Got{Tn.Odd{}, s}
    case 4n:
      W.Got{Tn.Garbled{}, s}
    case 5n:
      W.Got{Tn.Hung{}, s}
    case 6n+u:
      W.Bad{}

def get_probe(r: W.Dec<Nat>) -> W.Dec<Tn.Probe>:
  match r:
    case W.Got{t, s}:
      get_probe.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_heard.tag(t: Nat, s: String) -> W.Dec<Tn.Heard>:
  match t:
    case 0n:
      W.Got{Tn.Bye{}, s}
    case 1n:
      W.Got{Tn.Other{}, s}
    case 2n:
      W.Got{Tn.Eof{}, s}
    case 3n:
      W.Got{Tn.Lost{}, s}
    case 4n+u:
      W.Bad{}

def get_heard(r: W.Dec<Nat>) -> W.Dec<Tn.Heard>:
  match r:
    case W.Got{t, s}:
      get_heard.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_launch.tag(t: Nat, s: String) -> W.Dec<Tn.Launch>:
  match t:
    case 0n:
      W.Got{Tn.Bound{}, s}
    case 1n:
      W.Got{Tn.Adopted{}, s}
    case 2n+u:
      W.Bad{}

def get_launch(r: W.Dec<Nat>) -> W.Dec<Tn.Launch>:
  match r:
    case W.Got{t, s}:
      get_launch.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def seen.pinged(r: W.Dec<Tn.Probe>) -> W.Dec<Tn.Seen>:
  match r:
    case W.Got{p, s}:
      W.Got{Tn.Pinged{p}, s}
    case W.Bad{}:
      W.Bad{}

def seen.heard(r: W.Dec<Tn.Heard>) -> W.Dec<Tn.Seen>:
  match r:
    case W.Got{h, s}:
      W.Got{Tn.ShutHeard{h}, s}
    case W.Bad{}:
      W.Bad{}

def seen.came(r: W.Dec<Tn.Launch>) -> W.Dec<Tn.Seen>:
  match r:
    case W.Got{l, s}:
      W.Got{Tn.Came{l}, s}
    case W.Bad{}:
      W.Bad{}

def get_seen.tag(t: Nat, s: String) -> W.Dec<Tn.Seen>:
  match t:
    case 0n:
      seen.pinged(get_probe(W.get_nat(s)))
    case 1n:
      seen.heard(get_heard(W.get_nat(s)))
    case 2n:
      seen.came(get_launch(W.get_nat(s)))
    case 3n:
      W.Got{Tn.NoSpawn{}, s}
    case 4n:
      W.Got{Tn.Locked{}, s}
    case 5n+u:
      W.Bad{}

def get_seen.go(r: W.Dec<Nat>) -> W.Dec<Tn.Seen>:
  match r:
    case W.Got{t, s}:
      get_seen.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the outcome at the start of s
def get_seen(s: String) -> W.Dec<Tn.Seen>:
  get_seen.go(W.get_nat(s))

# what an open asks for
type Open is Data:
  ONeed{mine: String}
  OSeat{}

def open.need(r: W.Dec<String>) -> W.Dec<Open>:
  match r:
    case W.Got{m, s}:
      W.Got{ONeed{m}, s}
    case W.Bad{}:
      W.Bad{}

def get_open.tag(t: Nat, s: String) -> W.Dec<Open>:
  match t:
    case 0n:
      open.need(W.get_str(s))
    case 1n:
      W.Got{OSeat{}, s}
    case 2n+u:
      W.Bad{}

def get_open.go(r: W.Dec<Nat>) -> W.Dec<Open>:
  match r:
    case W.Got{t, s}:
      get_open.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the open at the start of s
def get_open(s: String) -> W.Dec<Open>:
  get_open.go(W.get_nat(s))

# Encoder
# -------

def got.tag(g: Tn.Got) -> Nat:
  match g:
    case Tn.Started{}:
      0n
    case Tn.Joined{}:
      1n
    case Tn.Replaced{}:
      2n

def why.tag(w: Tn.Why) -> Nat:
  match w:
    case Tn.WhyIo{}:
      0n
    case Tn.WhyProtocol{}:
      1n
    case Tn.WhyMistagged{}:
      2n
    case Tn.WhyVacant{}:
      3n
    case Tn.WhySpawn{}:
      4n

def put_do(d: Tn.Do) -> String:
  match d:
    case Tn.DoPing{}:
      W.put_nat(0n, "")
    case Tn.DoShutdown{}:
      W.put_nat(1n, "")
    case Tn.DoLaunch{}:
      W.put_nat(2n, "")
    case Tn.DoUse{g}:
      W.put_nat(3n, W.put_nat(got.tag(g), ""))
    case Tn.DoFail{w}:
      W.put_nat(4n, W.put_nat(why.tag(w), ""))
    case Tn.DoLock{}:
      W.put_nat(5n, "")
    case Tn.DoAdopt{}:
      W.put_nat(6n, "")
    case Tn.DoTake{}:
      W.put_nat(7n, "")
    case Tn.DoFault{}:
      W.put_nat(8n, "")
    case Tn.DoNothing{}:
      W.put_nat(9n, "")

# The stepper
# -----------

# the run, or a refused open
type St is Data:
  Live{r: Tn.Run}
  Refused{}

def reply(r: Tn.Run & Tn.Do) -> St & String:
  (x, d) = r
  (Live{x}, put_do(d))

def open.of(o: Open) -> St & String:
  match o:
    case ONeed{m}:
      reply(Tn.need(m))
    case OSeat{}:
      reply(Tn.seat())

def open.end(done: Bool, o: Open) -> St & String:
  match done:
    case True{}:
      open.of(o)
    case False{}:
      (Refused{}, W.err("tiny_run: malformed open"))

def open.got(r: W.Dec<Open>) -> St & String:
  match r:
    case W.Got{o, rest}:
      open.end(W.end(rest), o)
    case W.Bad{}:
      (Refused{}, W.err("tiny_run: malformed open"))

# open: a need's run, or a seat run; the reply is what Rust does first
def open(input: String) -> St & String:
  open.got(get_open(input))

def step.end(done: Bool, +x: Tn.Run, s: Tn.Seen) -> St & String:
  match done:
    case True{}:
      reply(Tn.step_run(x, s))
    case False{}:
      (Live{x}, W.err("tiny_run: malformed event"))

def step.got(+x: Tn.Run, r: W.Dec<Tn.Seen>) -> St & String:
  match r:
    case W.Got{s, rest}:
      step.end(W.end(rest), x, s)
    case W.Bad{}:
      (Live{x}, W.err("tiny_run: malformed event"))

# step: one outcome; the reply is what Rust does next
def step(st: St, input: String) -> St & String:
  match st:
    case Live{x}:
      step.got(x, get_seen(input))
    case Refused{}:
      (Refused{}, W.err("tiny_run: the open was refused"))
