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

# The model's terms, pinned
# -------------------------
# A second fresh adversary (SpecCheckJob) made an output of 0 bytes end the
# job as exited with code 0 while `J.done` answered False for every job:
# job_step_out_live read the step only through `J.done`, and no law tied
# the model's runs (`go`, `ends.go`, `run`, `ends`), which the S2 laws
# state, to `step`. The accessors and the runs are pinned here.

def kept_spec(j: Jb.J) -> Nat:
  match j:
    case Jb.Live{k, d}:
      k
    case Jb.Ended{k, d, e}:
      k

def dropped_spec(j: Jb.J) -> Nat:
  match j:
    case Jb.Live{k, d}:
      d
    case Jb.Ended{k, d, e}:
      d

def done_spec(j: Jb.J) -> Bool:
  match j:
    case Jb.Live{k, d}:
      False{}
    case Jb.Ended{k, d, e}:
      True{}

# LAW job_terms_exact: the model's accessors the laws read are the fields they name: the bytes
# kept, the bytes dropped, their sum, and whether the job ended
# EXCLUDES: an accessor that hides an end or reports other counts than the job holds (an output
#   that ends the job passing job_step_out_live)
law job_terms_exact:
  for +j: Jb.J
  {Jb.J.kept(j) == kept_spec(j) : Nat} & {Jb.J.dropped(j) == dropped_spec(j) : Nat} & {Jb.J.total(j) == Nat.add(kept_spec(j), dropped_spec(j)) : Nat} & {Jb.J.done(j) == done_spec(j) : Bool}

# LAW job_step_out_stays_live: output leaves a live job live: the step's result is a live job
# EXCLUDES: an output that ends the job (an end reported, a later exit dropped)
law job_step_out_stays_live:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {done_spec(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})) == False{} : Bool}

# LAW job_runs_are_steps: the model's runs, which the S2 laws state, are the steps one event at a
# time from a new job, and the ends they report are the ends each step reports, in order
# EXCLUDES: S2 laws that hold of a run that is not the step Rust runs
law job_runs_are_steps:
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for +es: List<&2, Jb.JEv>
  {Jb.go(Nil{}, cap, j) == j : Jb.J} & {Jb.go(e <> es, cap, j) == Jb.go(es, cap, Jb.step(cap, j, e)) : Jb.J} & {Jb.ends.go(Nil{}, cap, j) == Nil{} : List<&2, Jb.End>} & {Jb.ends.go(e <> es, cap, j) == List.append(&2, Jb.End, Jb.ends.of(j, e), Jb.ends.go(es, cap, Jb.step(cap, j, e))) : List<&2, Jb.End>} & {Jb.run(cap, es) == Jb.go(es, cap, Jb.Live{0n, 0n}) : Jb.J} & {Jb.ends(cap, es) == Jb.ends.go(es, cap, Jb.Live{0n, 0n}) : List<&2, Jb.End>}

# LAW job_feed_past_bound: a job whose counts are already past the bound t takes no more
# output: its counts stay as they are (Rust never holds such a job: job_feed_bounded)
# EXCLUDES: counts that grow past the bound, or bytes invented, from a job already past it (a
#   fourth fresh adversary's `feed` passed every other law)
law job_feed_past_bound:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for past: {Nat.is_lt(t, Nat.add(k, d)) == True{} : Bool}
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.Live{k, d} : Jb.J}
