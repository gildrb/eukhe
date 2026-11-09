# eukhe: the laws of area tiny, section elect: the choices of one
# process's election and of a started worker's seat (bend/tiny.bend
# section 3), each stated as the step of the run (Tn.step_run, bend/tiny.bend
# section 4, the step the stepper bend/ffi_tiny_run.bend answers) on the
# outcome its phase waits for; the requirements R1-R7 of the election

# (S9) One process's election
# ---------------------------
# bend/tiny.bend sections 3 and 4, run as the compiled core by the
# stepper bend/ffi_tiny_run.bend (crates/eukhe-tiny election.rs,
# worker.rs `bind`). Every input is free: any probe of the socket with
# any tag, any launch tag, any answer to a shutdown, any start and
# launch, any outcomes in any order, from any state of a run.
#
# Sources: crates/eukhe-tiny/src/election.rs (`Met` and `probe`: which
# ping outcome is which probe; `ensure`, `failure`, `seat`: what Rust
# does with each reply) and worker.rs `bind`; omp
# packages/coding-agent/src/subprocess/shared-worker.ts
# probeSharedWorker:220-226 (a worker is live for a process exactly when
# its pong carries the process's launch tag, compared as strings; a pong
# of another tag is shut down and replaced). Eukhe adds what omp folds
# into "absent": a socket that fails otherwise or answers out of protocol
# is an IO error (R1, R4, R6).
#
# R1: a worker that answers with the process's tag (the same text, char
#     by char) is joined; one with another tag is replaced; with no
#     worker (no socket, a refused one, or one that hangs up on the ping)
#     the process starts one; a socket that fails otherwise or speaks out
#     of protocol is an IO error, never a join or a start.
#     [tiny_run_own_tag_used, tiny_run_other_tag_replaced,
#     tiny_run_no_worker, tiny_run_socket_fails, tiny_elect_is_worker_model]
# R2: a shutdown answered with bye, or cut by the worker's own exit, lets
#     the start go on; another answer is out of protocol; another failure
#     is an IO error. [tiny_run_shutdown_answered]
# R3: a start the process made gets Started (first worker) or Replaced
#     (replacement) when its worker bound the socket, Joined when another
#     worker took the socket first. [tiny_run_launch_ended,
#     tiny_run_own_tag_used, tiny_run_is_model]
# R4: after a start, only a worker with the process's tag is used; another
#     tag or no worker fails the start; a failing socket is an IO error.
#     [tiny_run_own_tag_used, tiny_run_other_tag_replaced,
#     tiny_run_no_worker, tiny_run_socket_fails]
# R6: a started worker leaves a live worker of any tag in place (it is
#     adopted), takes a socket with no live worker, and fails on a socket
#     that fails otherwise or speaks out of protocol.
#     [tiny_seat_adopts_live, tiny_run_no_worker, tiny_run_socket_fails,
#     tiny_seat_under_lock]
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
#     a seat binds only under the lock. [the laws above;
#     laws/tiny/run.bend: tiny_run_waits, tiny_run_safe,
#     tiny_run_at_most_once, tiny_run_ends_once, tiny_seat_under_lock,
#     tiny_run_is_model; the anchor tiny_run_example; a need's and a
#     seat's first reply: tiny_run_entry_open]
# R5: the entry answers each open and outcome Rust writes with the run of
#     R7, reads exactly it and nothing after it, and answers any other
#     input with the exact error form, keeping the run.
#     [laws/tiny/run.bend: tiny_run_entry_*]

import Base
import ../../bend/tiny.bend as Tn
import ../base.bend as LawsBase

# Spec helpers
# ------------

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

# Laws: what a ping decides (R1, R4, R6)
# --------------------------------------
# Each law below is about the run's step (Tn.step_run) of a run of launch
# tag m (any text) in the phase that waits for a ping: the first ping of
# a need (Probing), the check after a start that got g (Checking{g}), the
# ping under the bind lock of a seat run (Seating).

# LAW tiny_run_own_tag_used (R1, R4): a ping that a worker answers with
# the run's own launch tag m (the very same text) is used and ends the
# run: on a need's first ping the need joins that worker (DoUse Joined);
# on the check after a start that got g, the need is served with g
# EXCLUDES: restart churn (a worker of the process's own tag shut down or
#   started over); a started worker of the right tag not used; a check
#   that reports another outcome than the start's
law tiny_run_own_tag_used:
  for +m: String
  for +g: Tn.Got
  {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Pong{m}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{Tn.Joined{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Pong{m}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{g}) : Tn.Run & Tn.Do}

# LAW tiny_run_other_tag_replaced (R1, R4): a ping that a worker answers
# with a tag t that is not the run's launch tag m (any other string, the
# type's own equality) is never used: on a need's first ping the run
# shuts that worker down (and then waits for its answer); on the check
# after a start the start fails as mistagged
# EXCLUDES: a stale worker of another tag served (tags compared by prefix,
#   by length, case-folded, or not at all); a mistagged worker after a
#   start taken for a success or for a vacant socket
law tiny_run_other_tag_replaced:
  for +m: String
  for +t: String
  for +g: Tn.Got
  for ne: {t != m : String}
  {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Pong{t}}) == (Tn.Run{m, Tn.Shutting{}}, Tn.DoShutdown{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Pong{t}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyMistagged{}}) : Tn.Run & Tn.Do}

# LAW tiny_run_no_worker (R1, R4, R6): a ping that shows no worker (no
# socket or a refused one: Missing; a connection closed or failed on the
# ping: Hung) makes a need's first ping launch a first worker, fails the
# check after a start as vacant, and makes a seat run take the socket
# EXCLUDES: a hung-up worker taken for an IO error or for a live one; a
#   need that fails instead of starting a worker; a start reported a
#   success with no worker there; a seat that leaves a free socket
law tiny_run_no_worker:
  for +m: String
  for +g: Tn.Got
  {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Missing{}}) == (Tn.Run{m, Tn.Launching{Tn.First{}}}, Tn.DoLaunch{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Hung{}}) == (Tn.Run{m, Tn.Launching{Tn.First{}}}, Tn.DoLaunch{}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Missing{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyVacant{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Hung{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyVacant{}}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Missing{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoTake{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Hung{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoTake{}) : Tn.Run & Tn.Do}

# LAW tiny_run_socket_fails (R1, R4, R6): a ping whose connect failed
# otherwise (Unreachable), or that a worker answered with another reply
# (Odd) or with no line of the protocol (Garbled), ends a need's run as
# an IO error, on the first ping and on the check after a start, and
# ends a seat run as a fault
# EXCLUDES: a failing socket taken for a missing worker (a second worker
#   started beside a live one that answers out of protocol), for a live
#   worker (joined or adopted), or reported as another failure
law tiny_run_socket_fails:
  for +m: String
  for +g: Tn.Got
  {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Unreachable{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Odd{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Garbled{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Unreachable{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Odd{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Garbled{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Unreachable{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFault{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Odd{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFault{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Garbled{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFault{}) : Tn.Run & Tn.Do}

# LAW tiny_seat_adopts_live (R6, R7): a seat run (any tag m) that gets
# the bind lock pings the socket, and a ping that a worker of any tag t
# answers leaves that worker in place (adopted) and ends the seat
# EXCLUDES: a seat that never pings once it holds the lock; a live worker
#   of another build replaced by a started one (its socket removed: two
#   workers fighting over one socket)
law tiny_seat_adopts_live:
  for +m: String
  for +t: String
  {Tn.step_run(Tn.Run{m, Tn.Locking{}}, Tn.Locked{}) == (Tn.Run{m, Tn.Seating{}}, Tn.DoPing{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{Tn.Pong{t}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoAdopt{}) : Tn.Run & Tn.Do}

# Laws: a shutdown's answer and a launch (R2, R3)
# -----------------------------------------------

# LAW tiny_run_shutdown_answered (R2): in a need's run (any tag m) that
# shut a worker of another tag down, an answer bye or the connection
# closed by the worker's own exit (Eof) launches a replacement; another
# answer fails the need as out of protocol; any other failure of the
# connection (Lost) as an IO error
# EXCLUDES: a start on top of a worker that answered the shutdown out of
#   protocol; an error for a worker that exited on its own meanwhile; a
#   replacement launched as a first worker (reported Started)
law tiny_run_shutdown_answered:
  for +m: String
  {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, Tn.ShutHeard{Tn.Bye{}}) == (Tn.Run{m, Tn.Launching{Tn.Again{}}}, Tn.DoLaunch{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, Tn.ShutHeard{Tn.Eof{}}) == (Tn.Run{m, Tn.Launching{Tn.Again{}}}, Tn.DoLaunch{}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, Tn.ShutHeard{Tn.Other{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyProtocol{}}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, Tn.ShutHeard{Tn.Lost{}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyIo{}}) : Tn.Run & Tn.Do}

# LAW tiny_run_launch_ended (R3, R7): a launch that ended pings again and
# carries what the start got into the check: a first worker that bound
# the socket Started, a replacement that bound it Replaced, a worker
# that found another one on the socket first (adopted) Joined, whichever
# start it was (f); a launch that failed fails the need (any tag m)
# EXCLUDES: a replacement reported as a first start, an adopted worker
#   reported as started by this process; a launch used without the check
#   ping; a failed launch launched again or reported as another failure
law tiny_run_launch_ended:
  for +m: String
  for +f: Tn.Fresh
  {Tn.step_run(Tn.Run{m, Tn.Launching{Tn.First{}}}, Tn.Came{Tn.Bound{}}) == (Tn.Run{m, Tn.Checking{Tn.Started{}}}, Tn.DoPing{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Launching{Tn.Again{}}}, Tn.Came{Tn.Bound{}}) == (Tn.Run{m, Tn.Checking{Tn.Replaced{}}}, Tn.DoPing{}) : Tn.Run & Tn.Do} &
  {Tn.step_run(Tn.Run{m, Tn.Launching{f}}, Tn.Came{Tn.Adopted{}}) == (Tn.Run{m, Tn.Checking{Tn.Joined{}}}, Tn.DoPing{}) : Tn.Run & Tn.Do} & {Tn.step_run(Tn.Run{m, Tn.Launching{f}}, Tn.NoSpawn{}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhySpawn{}}) : Tn.Run & Tn.Do}

# Laws: the worker model (R1, R3)
# -------------------------------

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
