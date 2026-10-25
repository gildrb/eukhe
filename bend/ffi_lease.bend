# ffi_lease: the stepper of the compiled Bend core for the chat's root-turn
# lease (bend/lease.bend), kept by the chat memory's owner
# (crates/eukhe-core/src/memory/service/turn.rs `Turns`): its state is the
# model's lease, kept in the Bend heap. Each step is one event, run by
# `M.answer`; the reply is what the owner acts on. The codec is the wire
# format of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    nothing                                 reply: empty
#   step    Ev                                      reply: an ask's key
#                                                   (Nat), then Answer;
#                                                   any other event: Answer
#   Ev      0, origin: Nat (an ask) | 1, key: Nat (a release)
#           | 2, origin: Nat (a crash)
#   Answer  grant: Maybe<Nat>, ended: List<Nat>
#
# The owner sends no stop: it learns that a waiter stopped waiting only
# when a grant cannot reach it, and then releases that lease. A malformed
# event, or one with input left over, answers the error form and keeps
# the state; an open with input opens the refused state, which answers
# every step with the error form. laws/lease.bend (lease_entry_*) pins
# the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./lease.bend as M

# Decoder
# -------

def get_ev.ask(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{o, s}:
      W.Got{M.Ask{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.release(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{k, s}:
      W.Got{M.Release{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.crash(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{o, s}:
      W.Got{M.Crash{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.Ev>:
  match t:
    case 0n:
      get_ev.ask(W.get_nat(s))
    case 1n:
      get_ev.release(W.get_nat(s))
    case 2n:
      get_ev.crash(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

# Encoders
# --------

def put_grant(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{k}:
      W.put_nat(1n, W.put_nat(k, rest))

def put_answer(a: M.Answer) -> String:
  match a:
    case M.Answer{g, d}:
      put_grant(g, W.put_list(~Nat, ~W.put_nat, d, ""))

# an ask's reply leads with the key it got (the next key before it)
def put_reply(e: M.Ev, n: Nat, a: M.Answer) -> String:
  match e:
    case M.Ask{o}:
      W.put_nat(n, put_answer(a))
    case M.Release{j}:
      put_answer(a)
    case M.Stop{j}:
      put_answer(a)
    case M.Crash{p}:
      put_answer(a)

# The stepper
# -----------

# the lease, or a refused open
type St is Data:
  Live{s: M.L}
  Shut{}

def fail() -> String:
  W.err("lease: malformed event")

def open.go(done: Bool) -> St & String:
  match done:
    case True{}:
      (Live{M.L.empty()}, "")
    case False{}:
      (Shut{}, W.err("lease: the open takes no input"))

# open: a free lease, no waiter, the first key next
def open(input: String) -> St & String:
  open.go(W.end(input))

def step.reply(e: M.Ev, n: Nat, r: M.L & M.Answer) -> St & String:
  (s, a) = r
  (Live{s}, put_reply(e, n, a))

def step.end(done: Bool, +s: M.L, +e: M.Ev) -> St & String:
  match done:
    case True{}:
      step.reply(e, M.L.next(s), M.answer(s, e))
    case False{}:
      (Live{s}, fail())

def step.ev(s: M.L, r: W.Dec<M.Ev>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), s, e)
    case W.Bad{}:
      (Live{s}, fail())

# step: one event; the reply is what the owner acts on
def step(st: St, input: String) -> St & String:
  match st:
    case Live{s}:
      step.ev(s, get_ev(input))
    case Shut{}:
      (Shut{}, W.err("lease: the open was refused"))
