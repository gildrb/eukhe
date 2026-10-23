# eukhe: the laws of area job

import Base
import ../bend/ffi_job.bend as FJb
import ../bend/job.bend as Jb
import ./base.bend as LawsBase

# (S2) Jobs and limits
# --------------------
# docs/runtime.md S2, the model in bend/job.bend. Every event is free:
# any output size, exit, kill or tick, in any order; any output cap or
# the opt-out; any budget; any tool call stream; any job table.

# LAW: with a cap, a job keeps at most cap bytes of its output
law job_output_bounded:
  for +c: Nat
  for es: List<&2, Jb.JEv>
  {Nat.is_le(Jb.J.kept(Jb.run(Some{c}, es)), c) == True{} : Bool}

# LAW: no output is lost in silence: the bytes kept plus the bytes
# counted as dropped are every byte the job wrote before it ended
law job_no_silent_loss:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))) == Jb.produced(es) : Nat}

# LAW: with the opt-out, a job drops nothing
law job_optout_keeps_all:
  for es: List<&2, Jb.JEv>
  {Jb.J.dropped(Jb.run(None{}, es)) == 0n : Nat}

# LAW: a cap drops nothing from output that fits
law job_cap_drops_only_excess:
  for +c: Nat
  for +es: List<&2, Jb.JEv>
  for fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}
  {Jb.J.dropped(Jb.run(Some{c}, es)) == 0n : Nat}

# LAW: a job reports exactly one end once it exits or is killed, and none
# before
law job_ends_once:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {List.length(&2, Jb.End, Jb.ends(cap, es)) == Jb.once(Jb.has_end(es)) : Nat}

# LAW: an ended job stays as it ended: no late output, no second end
law job_end_is_final:
  for +cap: Maybe<&2, Nat>
  for +pre: List<&2, Jb.JEv>
  for post: List<&2, Jb.JEv>
  for ended: {Jb.has_end(pre) == True{} : Bool}
  {Jb.run(cap, List.append(&2, Jb.JEv, pre, post)) == Jb.run(cap, pre) : Jb.J}

# LAW: a kill ends a live job at once, as killed, with its output kept
law job_kill_ends_now:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  {Jb.step(cap, Jb.Live{k, d}, Jb.Kill{}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J}

# LAW: a blocking call returns once its budget of ticks passed: it never
# blocks longer
law call_blocks_at_most_budget:
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}
  {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}

# LAW: a call that settles in time reports the job's own end, and the job
# has no other end
law call_settles_with_job:
  for +cap: Maybe<&2, Nat>
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for +x: Jb.End
  for settled: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}
  {Jb.ends(cap, es) == [x] : List<&2, Jb.End>}

# LAW: a tool call journals at most two records: its start and one final
# record; no delta is journaled
law stream_journals_two:
  for es: List<&2, Jb.CEv>
  {Nat.is_le(List.length(&2, Jb.CRec, Jb.journal(es)), 2n) == True{} : Bool}

# LAW: a tool call settles exactly once when it ends (result or cancel),
# and not before
law stream_settles_once:
  for +es: List<&2, Jb.CEv>
  {Jb.settles(Jb.journal(es)) == Jb.once(Jb.c.ends(es)) : Nat}

# LAW: the final record carries everything the stream carried: every
# result byte, every warning, all usage
law stream_settle_carries_all:
  for +es: List<&2, Jb.CEv>
  for ended: {Jb.c.ends(es) == True{} : Bool}
  {Jb.carried(Jb.journal(es)) == Some{Jb.Tally{Jb.c.bytes(es), Jb.c.warns(es), Jb.c.usage(es)}} : Maybe<&2, Jb.Tally>}

# LAW: after a rewind, every running job is a job of the target tree: no
# orphan job runs on
law rewind_stops_orphans:
  for +js: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}

# LAW: a rewind leaves every job of the target tree as it was
law rewind_keeps_target_jobs:
  for +js: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}

# The step the Rust jobs run is `feed` (bend/job.bend): `step` with a
# job's bytes kept plus dropped held to t (t = 10^14 - 1 in the compiled
# core: the largest Nat its wire carries). Every law below holds for every t.

# an event that writes output
def JobWrites(e: Jb.JEv) -> Bool:
  match e:
    case Jb.Out{n}:
      True{}
    case Jb.Quit{c}:
      False{}
    case Jb.Kill{}:
      False{}
    case Jb.Tick{}:
      False{}

# LAW: output that fits below t is the step: nothing is cut
law job_feed_fits:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}

# LAW: an event that writes no output is the step
law job_feed_no_output:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for j: Jb.J
  for e: Jb.JEv
  for quiet: {JobWrites(e) == False{} : Bool}
  {Jb.feed(t, cap, j, e) == Jb.step(cap, j, e) : Jb.J}

# LAW: an ended job stays as it ended
law job_feed_ended:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +x: Jb.End
  for e: Jb.JEv
  {Jb.feed(t, cap, Jb.Ended{k, d, x}, e) == Jb.Ended{k, d, x} : Jb.J}

# LAW: any output is a step on a part of it, so the cap laws above hold
# for what the Rust jobs count
law job_feed_is_a_step:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  exs m: Nat
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{m}) : Jb.J}

# LAW: the bytes kept plus dropped never pass t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law job_feed_bounded:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for e: Jb.JEv
  for below: {Nat.is_le(Jb.J.total(j), t) == True{} : Bool}
  {Nat.is_le(Jb.J.total(Jb.feed(t, cap, j, e)), t) == True{} : Bool}

# LAW: output past t fills the counts to exactly t: they saturate
# EXCLUDES: output past t that is dropped whole or counted short
law job_feed_fills:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for below: {Nat.is_le(Nat.add(k, d), t) == True{} : Bool}
  for over: {Nat.is_lt(t, Nat.add(Nat.add(k, d), n)) == True{} : Bool}
  {Jb.J.total(Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n})) == t : Nat}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

def wire_job_fits(j: Jb.J) -> Bool:
  match j:
    case Jb.Live{k, d}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(d))
    case Jb.Ended{k, d, e}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(d))

def wire_ev_fits(e: Jb.JEv) -> Bool:
  match e:
    case Jb.Out{n}:
      LawsBase.wire_fits(n)
    case Jb.Quit{c}:
      True{}
    case Jb.Kill{}:
      True{}
    case Jb.Tick{}:
      True{}

# LAW: the job entry answers the held step and the ends the event reported
law job_entry:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(cap) == True{} : Bool}
  for hj: {wire_job_fits(j) == True{} : Bool}
  for he: {wire_ev_fits(e) == True{} : Bool}
  {FJb.ffi(FJb.put_req(t, cap, j, e)) == FJb.put_reply(Jb.feed(t, cap, j, e), Jb.ends.of(j, e)) : String}
