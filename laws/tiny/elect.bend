# eukhe: the laws of area tiny, section elect: the choices of one
# process's election and of a started worker's seat (bend/tiny.bend
# section 3); the requirements R1-R7 of the election

import Base
import ../../bend/tiny.bend as Tn
import ../base.bend as LawsBase

# (S9) One process's election
# ---------------------------
# bend/tiny.bend sections 3 and 4, run as the compiled core by the
# stepper bend/ffi_tiny_run.bend (crates/eukhe-tiny election.rs,
# worker.rs `bind`). Every input is free: any probe of the socket with
# any tag, any launch tag, any answer to a shutdown, any start and
# launch, any outcomes in any order, from any state of a run.
#
# R1: a worker that answers with the process's tag (the same text, char
#     by char) is joined; one with another tag is replaced; with no
#     worker (no socket, a refused one, or one that hangs up on the ping)
#     the process starts one; a socket that fails otherwise or speaks out
#     of protocol is an IO error, never a join or a start.
# R2: a shutdown answered with bye, or cut by the worker's own exit, lets
#     the start go on; another answer is out of protocol; another failure
#     is an IO error.
# R3: a start the process made gets Started (first worker) or Replaced
#     (replacement) when its worker bound the socket, Joined when another
#     worker took the socket first.
# R4: after a start, only a worker with the process's tag is used; another
#     tag or no worker fails the start; a failing socket is an IO error.
# R6: a started worker leaves a live worker of any tag in place (it is
#     adopted), takes a socket with no live worker, and fails on a socket
#     that fails otherwise or speaks out of protocol.
# R7: a run decides, from each outcome Rust reports, what Rust does next:
#     a need pings first; its ping decides by R1 (join: use the
#     connection; replace: shut the worker down; start: launch); a
#     shutdown's answer by R2 (launch, or fail); a launch that ended
#     pings again, and that ping decides by R4 with the outcome of R3; a
#     launch that failed fails the need. A seat run takes the bind lock
#     first, pings only once it holds it, and decides by R6. An outcome
#     the run does not wait for does nothing and leaves the run as it
#     is; an ended run does nothing. Whatever the order of the outcomes:
#     a run uses only a worker that answered with its tag, shuts down
#     only a worker of another tag, launches only on a socket with no
#     live worker, launches and shuts down at most once, ends once, and
#     a seat binds only under the lock.
# R5: the entry answers each open and outcome Rust writes with the run of
#     R7, reads exactly it and nothing after it, and answers any other
#     input with the exact error form, keeping the run.

# Spec helpers
# ------------

def sp_pong(b: Bool, j: Tn.Act, r: Tn.Act) -> Tn.Act:
  match b:
    case True{}:
      j
    case False{}:
      r

# R1
def sp_elect(p: Tn.Probe, +m: String) -> Tn.Act:
  match p:
    case Tn.Missing{}:
      Tn.Start{}
    case Tn.Unreachable{}:
      Tn.Broken{}
    case Tn.Pong{t}:
      sp_pong(LawsBase.text_same(t, m), Tn.Join{}, Tn.Replace{})
    case Tn.Odd{}:
      Tn.Broken{}
    case Tn.Garbled{}:
      Tn.Broken{}
    case Tn.Hung{}:
      Tn.Start{}

# R2
def sp_shut(h: Tn.Heard) -> Tn.Shut:
  match h:
    case Tn.Bye{}:
      Tn.Down{}
    case Tn.Other{}:
      Tn.Spoke{}
    case Tn.Eof{}:
      Tn.Down{}
    case Tn.Lost{}:
      Tn.Cut{}

# R3
def sp_launched(l: Tn.Launch, f: Tn.Fresh) -> Tn.Got:
  match l:
    case Tn.Adopted{}:
      Tn.Joined{}
    case Tn.Bound{}:
      match f:
        case Tn.First{}:
          Tn.Started{}
        case Tn.Again{}:
          Tn.Replaced{}

def sp_check(b: Bool) -> Tn.Check:
  match b:
    case True{}:
      Tn.Serving{}
    case False{}:
      Tn.Mistagged{}

# R4
def sp_confirm(p: Tn.Probe, +m: String) -> Tn.Check:
  match p:
    case Tn.Missing{}:
      Tn.Vacant{}
    case Tn.Unreachable{}:
      Tn.Faulty{}
    case Tn.Pong{t}:
      sp_check(LawsBase.text_same(t, m))
    case Tn.Odd{}:
      Tn.Faulty{}
    case Tn.Garbled{}:
      Tn.Faulty{}
    case Tn.Hung{}:
      Tn.Vacant{}

# R6
def sp_bind(p: Tn.Probe) -> Tn.Seat:
  match p:
    case Tn.Missing{}:
      Tn.Take{}
    case Tn.Unreachable{}:
      Tn.Fault{}
    case Tn.Pong{t}:
      Tn.Adopt{}
    case Tn.Odd{}:
      Tn.Fault{}
    case Tn.Garbled{}:
      Tn.Fault{}
    case Tn.Hung{}:
      Tn.Take{}

# what a need of the worker model gets from a choice whose start bound
def sp_need(a: Tn.Act) -> List<&2, Tn.Got>:
  match a:
    case Tn.Join{}:
      [Tn.Joined{}]
    case Tn.Replace{}:
      [Tn.Replaced{}]
    case Tn.Start{}:
      [Tn.Started{}]
    case Tn.Broken{}:
      Nil{}

# Laws: the choices
# -----------------

# LAW tiny_elect_spec (R1): the first choice of a process is the spec's:
# join its tag, replace another tag, start with no worker, an IO error on
# a failing socket
# EXCLUDES: tags compared by prefix, length or case; a hung-up worker
#   taken for an error, or a failing socket for a missing worker; a
#   worker of another tag joined
law tiny_elect_spec:
  for +p: Tn.Probe
  for +m: String
  {Tn.elect(p, m) == sp_elect(p, m) : Tn.Act}

# LAW tiny_shut_spec (R2): what a shutdown's answer means
# EXCLUDES: a start on top of a worker that answered out of protocol; an
#   error for a worker that exited on its own meanwhile
law tiny_shut_spec:
  for +h: Tn.Heard
  {Tn.shut(h) == sp_shut(h) : Tn.Shut}

# LAW tiny_launched_spec (R3): what a need that started a worker got
# EXCLUDES: a replacement reported as a first start, an adopted worker
#   reported as started by this process
law tiny_launched_spec:
  for +f: Tn.Fresh
  for +l: Tn.Launch
  {Tn.launched(f, l) == sp_launched(l, f) : Tn.Got}

# LAW tiny_confirm_spec (R4): after a start only a worker with the
# process's tag is used
# EXCLUDES: a stale worker of another tag used after a start; a vacant
#   socket taken for a running worker
law tiny_confirm_spec:
  for +p: Tn.Probe
  for +m: String
  {Tn.confirm(p, m) == sp_confirm(p, m) : Tn.Check}

# LAW tiny_bind_spec (R6): a started worker adopts a live worker of any
# tag and binds only a socket with no live worker
# EXCLUDES: two workers bound on one socket; a live worker's socket
#   removed; a failing socket taken for a free one
law tiny_bind_spec:
  for +p: Tn.Probe
  {Tn.bind(p) == sp_bind(p) : Tn.Seat}

# LAW tiny_elect_is_worker_model (R1, R3): a process's choice, with its
# start bound, is what the worker model's need gets: with a worker of tag
# t running and a need of tag m (the texts a and b name them: the same
# text exactly when t = m), and with no worker
# EXCLUDES: a process election that drifts from the worker model of
#   tiny_same_tag_joins and tiny_worker_current
law tiny_elect_is_worker_model:
  for +o: Nat
  for +t: Nat
  for +q: Nat
  for +m: Nat
  for +a: String
  for +b: String
  for named: {LawsBase.text_same(a, b) == Nat.is_eq(t, m) : Bool}
  {sp_need(Tn.elect(Tn.Pong{a}, b)) == Tn.got(Tn.Worker{o, t}, Tn.Need{q, m}) : List<&2, Tn.Got>} & {sp_need(Tn.elect(Tn.Missing{}, b)) == Tn.got(Tn.NoWorker{}, Tn.Need{q, m}) : List<&2, Tn.Got>}
