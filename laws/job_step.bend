# eukhe: the laws of area job (the step itself)
#
# laws/job.bend states a job's step mostly through runs from a new job
# (`run`, `ends`). The job entry (bend/ffi_job.bend, id 14) answers one
# step from any job Rust holds: `feed` and `ends.of`. Rust holds the job
# the entry answered and sends it the next event (JobState::step,
# crates/eukhe-core/src/durable/jobs/mod.rs). These laws pin that loop
# (`fed`, `fed_ends` below) and the step itself, for every job and event:
# what an exit, a kill, a tick and an output do, and which end an event
# reports. The requirements (A1-A12) are in the header of laws/job.bend.

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

# what Rust holds after it sends the events es one at a time to the job
# entry (which answers `feed`), from the job j it holds
def fed(es: List<&2, Jb.JEv>, +t: Nat, +cap: Maybe<&2, Nat>, j: Jb.J) -> Jb.J:
  match es:
    case Nil{}:
      j
    case e <> rest:
      fed(rest, t, cap, Jb.feed(t, cap, j, e))

# the ends the entry reported along that loop (it answers `ends.of` with
# each job), in order
def fed_ends(es: List<&2, Jb.JEv>, +t: Nat, +cap: Maybe<&2, Nat>, +j: Jb.J) -> List<&2, Jb.End>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, Jb.End, Jb.ends.of(j, e), fed_ends(rest, t, cap, Jb.feed(t, cap, j, e)))

# Laws
# ----

# LAW job_ends_of_exact (A4, A6): the ends an event reports are exactly the end its step made: one
# when it ends a live job, none otherwise (no end on output or a tick, no second end of an ended job)
law job_ends_of_exact:
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  {Jb.ends.of(j, e) == fresh_end(j, Jb.step(cap, j, e)) : List<&2, Jb.End>}

# LAW job_ended_ignores_events (A5): an ended job Rust holds stays exactly as it ended, with its
# counts and its end, whatever events it then sends the job entry (any bound t, any cap), and the
# entry reports no more end
# EXCLUDES: late output counted after an end, a second end, an end overwritten by a later kill or exit
law job_ended_ignores_events:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +x: Jb.End
  for +es: List<&2, Jb.JEv>
  {fed(es, t, cap, Jb.Ended{k, d, x}) == Jb.Ended{k, d, x} : Jb.J} & {fed_ends(es, t, cap, Jb.Ended{k, d, x}) == Nil{} : List<&2, Jb.End>}

# LAW job_kill_ends_killed (A4, A5): a kill sent to a live job with k bytes kept and d dropped ends
# it at once as killed with those counts; the entry reports exactly that one end, and no event after
# the kill changes the job or reports another end
# EXCLUDES: a kill read as an exit, a kill that loses or changes the counts, a kill that leaves the
#   job running, a later event that revives or re-ends it
law job_kill_ends_killed:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +es: List<&2, Jb.JEv>
  {fed(Jb.Kill{} <> es, t, cap, Jb.Live{k, d}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J} & {fed_ends(Jb.Kill{} <> es, t, cap, Jb.Live{k, d}) == [Jb.Killed{}] : List<&2, Jb.End>}

# LAW job_exit_ends_exited (A4, A5): an exit with code c sent to a live job with k bytes kept and d
# dropped ends it as exited with exactly c and those counts; the entry reports exactly that one end,
# and no event after the exit changes the job or reports another end
# EXCLUDES: an exit with another code (a word swapped, a default 0), an exit read as a kill, counts
#   lost at the exit, a later event that revives or re-ends the job
law job_exit_ends_exited:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +c: Jb.Code
  for +es: List<&2, Jb.JEv>
  {fed(Jb.Quit{c} <> es, t, cap, Jb.Live{k, d}) == Jb.Ended{k, d, Jb.Exited{c}} : Jb.J} & {fed_ends(Jb.Quit{c} <> es, t, cap, Jb.Live{k, d}) == [Jb.Exited{c}] : List<&2, Jb.End>}

# LAW job_tick_changes_nothing (A6): a tick changes no job and reports no end: from any job Rust
# holds, sending a tick and then any events gives the same job and the same ends as sending those
# events alone
# EXCLUDES: a tick that ends a job, counts bytes or resets the counts
law job_tick_changes_nothing:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +es: List<&2, Jb.JEv>
  {fed(Jb.Tick{} <> es, t, cap, j) == fed(es, t, cap, j) : Jb.J} & {fed_ends(Jb.Tick{} <> es, t, cap, j) == fed_ends(es, t, cap, j) : List<&2, Jb.End>}

# LAW job_out_stays_live (A6): output never ends a live job: after any output (any bound t, any cap)
# the job is live, with no fewer bytes kept and no fewer dropped than before, and the event reports
# no end
# EXCLUDES: an output that ends the job (an end reported, a later exit dropped), an output that lowers
#   a count
law job_out_stays_live:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  exs a: Nat
  exs b: Nat
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.Live{a, b} : Jb.J} & {Nat.is_le(k, a) == True{} : Bool} & {Nat.is_le(d, b) == True{} : Bool} & {Jb.ends.of(Jb.Live{k, d}, Jb.Out{n}) == Nil{} : List<&2, Jb.End>}

# LAW job_optout_keeps_output (A3): with the opt-out, an output of n bytes below the wire bound t
# (k + d + n <= t) is kept whole: the job becomes live with k + n bytes kept and the same d dropped
# EXCLUDES: an opt-out that cuts or drops output, counts written to the wrong field (kept read as
#   dropped), an output that ends the job
law job_optout_keeps_output:
  for +t: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}
  {Jb.feed(t, None{}, Jb.Live{k, d}, Jb.Out{n}) == Jb.Live{Nat.add(k, n), d} : Jb.J}

# LAW job_step_out_counts (A2): an output of n bytes adds exactly n to the bytes kept plus dropped,
# from any live job, under any cap
law job_step_out_counts:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {Jb.J.total(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})) == Nat.add(Nat.add(k, d), n) : Nat}

# LAW job_step_out_fits (A1): under a cap, an output that fits is kept whole
law job_step_out_fits:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(k, n), c) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == Nat.add(k, n) : Nat}

# LAW job_step_out_fills (A1): under a cap, an output that does not fit fills the cap exactly: every
# byte that fits is kept, none past the cap
law job_step_out_fills:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for below: {Nat.is_le(k, c) == True{} : Bool}
  for over: {Nat.is_lt(c, Nat.add(k, n)) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == c : Nat}

# LAW job_step_out_full (A1): under a cap, a job that holds the cap or more keeps no more output
law job_step_out_full:
  for +c: Nat
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for full: {Nat.is_le(c, k) == True{} : Bool}
  {Jb.J.kept(Jb.step(Some{c}, Jb.Live{k, d}, Jb.Out{n})) == k : Nat}

# LAW job_feed_past_bound (A7): a job whose counts are already past the bound t takes no more
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

# The model terms the job laws read
# ---------------------------------
# call_blocks_at_most_budget reads `ticks`; rewind_stops_orphans,
# rewind_keeps_target_jobs, job_rewind_stops_orphans and
# job_rewind_keeps_target_jobs read `elem`, `running_in` and `kept`. Each
# is fixed here by properties: how it splits over a joined list, and its
# value on one item, from the words of the term.

# LAW job_ticks_counts (A8): the ticks of an event list are counted one per tick: the ticks of two
# lists joined are the sum of their ticks; a tick counts one, an output, an exit or a kill none
# EXCLUDES: a tick count that is constant, skips ticks, or counts other events (a budget law that
#   holds vacuously)
law job_ticks_counts:
  for +xs: List<&2, Jb.JEv>
  for +ys: List<&2, Jb.JEv>
  for n: Nat
  for c: Jb.Code
  {Jb.ticks(List.append(&2, Jb.JEv, xs, ys)) == Nat.add(Jb.ticks(xs), Jb.ticks(ys)) : Nat} & {Jb.ticks([Jb.Tick{}]) == 1n : Nat} & {Jb.ticks([Jb.Out{n}]) == 0n : Nat} & {Jb.ticks([Jb.Quit{c}]) == 0n : Nat} & {Jb.ticks([Jb.Kill{}]) == 0n : Nat}

# LAW job_elem_finds_member (A9): a number is found in every list that holds it, wherever it stands
# EXCLUDES: a membership test that misses an id (a held job stopped)
law job_elem_finds_member:
  for +xs: List<&2, Nat>
  for +x: Nat
  for ys: List<&2, Nat>
  {Jb.elem(List.append(&2, Nat, xs, x <> ys), x) == True{} : Bool}

# LAW job_elem_only_members (A9): a number found in a list stands in it: the list is some items, the
# number, then some more
# EXCLUDES: a membership test that finds an id the list lacks (an orphan kept running)
law job_elem_only_members:
  for +ys: List<&2, Nat>
  for +x: Nat
  for found: {Jb.elem(ys, x) == True{} : Bool}
  exs xs: List<&2, Nat>
  exs zs: List<&2, Nat>
  {ys == List.append(&2, Nat, xs, x <> zs) : List<&2, Nat>}

# LAW job_running_in_each (A9): "every running slot is held" holds of two tables joined exactly when
# it holds of each; it holds of no slots and of a stopped slot; of a running slot exactly when its id
# is held
# EXCLUDES: a check that is constant, skips slots, or reads a stopped slot as running
law job_running_in_each:
  for +js: List<&2, Jb.Slot>
  for +ks: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  for +i: Nat
  {Jb.running_in(List.append(&2, Jb.Slot, js, ks), keep) == Bool.and(Jb.running_in(js, keep), Jb.running_in(ks, keep)) : Bool} & {Jb.running_in(Nil{}, keep) == True{} : Bool} & {Jb.running_in([Jb.Slot{i, False{}}], keep) == True{} : Bool} & {Jb.running_in([Jb.Slot{i, True{}}], keep) == Jb.elem(keep, i) : Bool}

# LAW job_kept_each (A9): "every held slot is as it was" holds of two pairs of tables of the same
# length joined exactly when it holds of each pair; of tables of different lengths never; of a table
# and itself always; of one slot whose id is not held whatever slot it had been
# EXCLUDES: a frame check that is constant, compares slots at other places, or ignores a length change
law job_kept_each:
  for +js: List<&2, Jb.Slot>
  for +ks: List<&2, Jb.Slot>
  for +js2: List<&2, Jb.Slot>
  for +ks2: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  for +s: Jb.Slot
  for same: {List.length(&2, Jb.Slot, js) == List.length(&2, Jb.Slot, ks) : Nat}
  {Jb.kept(List.append(&2, Jb.Slot, js, js2), List.append(&2, Jb.Slot, ks, ks2), keep) == Bool.and(Jb.kept(js, ks, keep), Jb.kept(js2, ks2, keep)) : Bool} & {Jb.kept(Nil{}, s <> ks, keep) == False{} : Bool} & {Jb.kept(s <> js, Nil{}, keep) == False{} : Bool} & {Jb.kept(js, js, keep) == True{} : Bool}

# LAW job_kept_held_same (A9): one slot whose id is held is as it was exactly when it is the same
# slot: the same id and the same running flag
# EXCLUDES: a frame check that lets a held job stop or change id
law job_kept_held_same:
  for +i: Nat
  for +r: Bool
  for +s: Jb.Slot
  for +keep: List<&2, Nat>
  for held: {Jb.elem(keep, i) == True{} : Bool}
  for ok: {Jb.kept([Jb.Slot{i, r}], [s], keep) == True{} : Bool}
  {s == Jb.Slot{i, r} : Jb.Slot}

# LAW job_kept_unheld_free (A9): one slot whose id is not held is as it was whatever slot it had been
# EXCLUDES: a frame check that also freezes the jobs a rewind must stop
law job_kept_unheld_free:
  for +i: Nat
  for +r: Bool
  for +s: Jb.Slot
  for +keep: List<&2, Nat>
  for free: {Jb.elem(keep, i) == False{} : Bool}
  {Jb.kept([Jb.Slot{i, r}], [s], keep) == True{} : Bool}

# LAW job_step_out_live: output never ends a job
law job_step_out_live:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  {Jb.J.done(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})) == False{} : Bool}

def done_spec(j: Jb.J) -> Bool:
  match j:
    case Jb.Live{k, d}:
      False{}
    case Jb.Ended{k, d, e}:
      True{}

def dropped_spec(j: Jb.J) -> Nat:
  match j:
    case Jb.Live{k, d}:
      d
    case Jb.Ended{k, d, e}:
      d

def kept_spec(j: Jb.J) -> Nat:
  match j:
    case Jb.Live{k, d}:
      k
    case Jb.Ended{k, d, e}:
      k

# LAW job_terms_exact: the model's accessors the laws read are the fields they name: the bytes
# kept, the bytes dropped, their sum, and whether the job ended
# EXCLUDES: an accessor that hides an end or reports other counts than the job holds (an output
#   that ends the job passing job_step_out_live)
law job_terms_exact:
  for +j: Jb.J
  {Jb.J.kept(j) == kept_spec(j) : Nat} & {Jb.J.dropped(j) == dropped_spec(j) : Nat} & {Jb.J.total(j) == Nat.add(kept_spec(j), dropped_spec(j)) : Nat} & {Jb.J.done(j) == done_spec(j) : Bool}

# LAW job_runs_are_steps: the model's runs, which the S2 laws state, are the steps one event at a
# time from a new job, and the ends they report are the ends each step reports, in order
# EXCLUDES: S2 laws that hold of a run that is not the step Rust runs
law job_runs_are_steps:
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for +es: List<&2, Jb.JEv>
  {Jb.go(Nil{}, cap, j) == j : Jb.J} & {Jb.go(e <> es, cap, j) == Jb.go(es, cap, Jb.step(cap, j, e)) : Jb.J} & {Jb.ends.go(Nil{}, cap, j) == Nil{} : List<&2, Jb.End>} & {Jb.ends.go(e <> es, cap, j) == List.append(&2, Jb.End, Jb.ends.of(j, e), Jb.ends.go(es, cap, Jb.step(cap, j, e))) : List<&2, Jb.End>} & {Jb.run(cap, es) == Jb.go(es, cap, Jb.Live{0n, 0n}) : Jb.J} & {Jb.ends(cap, es) == Jb.ends.go(es, cap, Jb.Live{0n, 0n}) : List<&2, Jb.End>}
