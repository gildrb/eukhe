# eukhe: the laws of area job (the step itself)
#
# laws/job.bend states a job's step mostly through runs from a new job
# (`run`, `ends`). The job entry (bend/ffi_job.bend, id 14) answers one
# step from any job Rust holds: `feed` (pinned to `step` by the job_feed_*
# laws) and `ends.of`. These laws pin `step` and `ends.of` themselves, for
# every job and event: what an exit, a kill, a tick and an output do, and
# which end an event reports.

import Base
import ../bend/job.bend as Jb

# Terms
# -----

# the end a step made: the end of a job that was live before it and ended
# after it; none otherwise
def fresh_end(j: Jb.J, x: Jb.J) -> List<&2, Jb.End>:
  match j:
    case Jb.Live{k, d}:
      match x:
        case Jb.Live{a, b}:
          Nil{}
        case Jb.Ended{a, b, e}:
          [e]
    case Jb.Ended{k, d, e}:
      Nil{}

# Laws
# ----

# LAW job_ends_of_exact: the ends an event reports are exactly the end its step made: one when it
# ends a live job, none otherwise (no end on output or a tick, no second end of an ended job)
law job_ends_of_exact:
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  {Jb.ends.of(j, e) == fresh_end(j, Jb.step(cap, j, e)) : List<&2, Jb.End>}

# LAW job_step_exit_exact: an exit ends a live job as exited with exactly the code it reported,
# its counts kept
law job_step_exit_exact:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +c: Jb.Code
  {Jb.step(cap, Jb.Live{k, d}, Jb.Quit{c}) == Jb.Ended{k, d, Jb.Exited{c}} : Jb.J}

# LAW job_step_tick_exact: a tick changes no job
law job_step_tick_exact:
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  {Jb.step(cap, j, Jb.Tick{}) == j : Jb.J}

# LAW job_step_ended_exact: an ended job stays exactly as it ended, whatever the event
law job_step_ended_exact:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +x: Jb.End
  for +e: Jb.JEv
  {Jb.step(cap, Jb.Ended{k, d, x}, e) == Jb.Ended{k, d, x} : Jb.J}

# LAW job_step_out_live: output never ends a job
law job_step_out_live:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {Jb.J.done(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})) == False{} : Bool}

# LAW job_step_out_counts: an output of n bytes adds exactly n to the bytes kept plus dropped,
# from any live job, under any cap
law job_step_out_counts:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {Jb.J.total(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})) == Nat.add(Nat.add(k, d), n) : Nat}

# LAW job_step_optout_keeps: with the opt-out a job keeps every byte of an output
law job_step_optout_keeps:
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {Jb.J.kept(Jb.step(None{}, Jb.Live{k, d}, Jb.Out{n})) == Nat.add(k, n) : Nat}

# LAW job_step_out_fits: under a cap, an output that fits is kept whole
law job_step_out_fits:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(k, n), c) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == Nat.add(k, n) : Nat}

# LAW job_step_out_fills: under a cap, an output that does not fit fills the cap exactly: every
# byte that fits is kept, none past the cap
law job_step_out_fills:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for below: {Nat.is_le(k, c) == True{} : Bool}
  for over: {Nat.is_lt(c, Nat.add(k, n)) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == c : Nat}

# LAW job_step_out_full: under a cap, a job that holds the cap or more keeps no more output
law job_step_out_full:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for full: {Nat.is_le(c, k) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == k : Nat}
