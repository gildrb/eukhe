# eukhe: the laws of area job

import Base
import ../bend/ffi_job.bend as FJb
import ../bend/ffi_job_rewind.bend as FJr
import ../bend/ffi_job_wait.bend as FJw
import ../bend/job.bend as Jb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S2) Jobs and limits
# --------------------
# docs/runtime.md S2, the model in bend/job.bend. Every event is free:
# any output size, exit, kill or tick, in any order; any output cap or
# the opt-out; any budget; any tool call stream; any job table.

# LAW job_output_bounded: with a cap, a job keeps at most cap bytes of its output
law job_output_bounded:
  for +c: Nat
  for es: List<&2, Jb.JEv>
  {Nat.is_le(Jb.J.kept(Jb.run(Some{c}, es)), c) == True{} : Bool}

# LAW job_no_silent_loss: no output is lost in silence: the bytes kept plus the bytes
# counted as dropped are every byte the job wrote before it ended
law job_no_silent_loss:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))) == Jb.produced(es) : Nat}

# LAW job_optout_keeps_all: with the opt-out, a job drops nothing
law job_optout_keeps_all:
  for es: List<&2, Jb.JEv>
  {Jb.J.dropped(Jb.run(None{}, es)) == 0n : Nat}

# LAW job_cap_drops_only_excess: a cap drops nothing from output that fits
law job_cap_drops_only_excess:
  for +c: Nat
  for +es: List<&2, Jb.JEv>
  for fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}
  {Jb.J.dropped(Jb.run(Some{c}, es)) == 0n : Nat}

# LAW job_ends_once: a job reports exactly one end once it exits or is killed, and none
# before
law job_ends_once:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {List.length(&2, Jb.End, Jb.ends(cap, es)) == Jb.once(Jb.has_end(es)) : Nat}

# LAW job_end_is_final: an ended job stays as it ended: no late output, no second end
law job_end_is_final:
  for +cap: Maybe<&2, Nat>
  for +pre: List<&2, Jb.JEv>
  for post: List<&2, Jb.JEv>
  for ended: {Jb.has_end(pre) == True{} : Bool}
  {Jb.run(cap, List.append(&2, Jb.JEv, pre, post)) == Jb.run(cap, pre) : Jb.J}

# LAW job_kill_ends_now: a kill ends a live job at once, as killed, with its output kept
law job_kill_ends_now:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  {Jb.step(cap, Jb.Live{k, d}, Jb.Kill{}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J}

# LAW call_blocks_at_most_budget: a blocking call returns once its budget of ticks passed: it never
# blocks longer
law call_blocks_at_most_budget:
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}
  {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}

# LAW call_settles_with_job: a call that settles in time reports the job's own end, and the job
# has no other end
law call_settles_with_job:
  for +cap: Maybe<&2, Nat>
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for +x: Jb.End
  for settled: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}
  {Jb.ends(cap, es) == [x] : List<&2, Jb.End>}

# LAW stream_journals_two: a tool call journals at most two records: its start and one final
# record; no delta is journaled
law stream_journals_two:
  for es: List<&2, Jb.CEv>
  {Nat.is_le(List.length(&2, Jb.CRec, Jb.journal(es)), 2n) == True{} : Bool}

# LAW stream_settles_once: a tool call settles exactly once when it ends (result or cancel),
# and not before
law stream_settles_once:
  for +es: List<&2, Jb.CEv>
  {Jb.settles(Jb.journal(es)) == Jb.once(Jb.c.ends(es)) : Nat}

# LAW stream_settle_carries_all: the final record carries everything the stream carried: every
# result byte, every warning, all usage
law stream_settle_carries_all:
  for +es: List<&2, Jb.CEv>
  for ended: {Jb.c.ends(es) == True{} : Bool}
  {Jb.carried(Jb.journal(es)) == Some{Jb.Tally{Jb.c.bytes(es), Jb.c.warns(es), Jb.c.usage(es)}} : Maybe<&2, Jb.Tally>}

# LAW rewind_stops_orphans: after a rewind, every running job is a job of the target tree: no
# orphan job runs on
law rewind_stops_orphans:
  for +js: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}

# LAW rewind_keeps_target_jobs: a rewind leaves every job of the target tree as it was
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

# LAW job_feed_fits: output that fits below t is the step: nothing is cut
law job_feed_fits:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}

# LAW job_feed_no_output: an event that writes no output is the step
law job_feed_no_output:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for j: Jb.J
  for e: Jb.JEv
  for quiet: {JobWrites(e) == False{} : Bool}
  {Jb.feed(t, cap, j, e) == Jb.step(cap, j, e) : Jb.J}

# LAW job_feed_ended: an ended job stays as it ended
law job_feed_ended:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +x: Jb.End
  for e: Jb.JEv
  {Jb.feed(t, cap, Jb.Ended{k, d, x}, e) == Jb.Ended{k, d, x} : Jb.J}

# LAW job_feed_is_a_step: any output is a step on a part of it, so the cap laws above hold
# for what the Rust jobs count
law job_feed_is_a_step:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  exs m: Nat
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{m}) : Jb.J}

# LAW job_feed_bounded: the bytes kept plus dropped never pass t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law job_feed_bounded:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for e: Jb.JEv
  for below: {Nat.is_le(Jb.J.total(j), t) == True{} : Bool}
  {Nat.is_le(Jb.J.total(Jb.feed(t, cap, j, e)), t) == True{} : Bool}

# LAW job_feed_fills: output past t fills the counts to exactly t: they saturate
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

# LAW job_entry: the job entry answers the held step and the ends the event reported
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

# ---- job: the entries Rust calls, over the laws' own spellers ----

# The job entry (bend/ffi_job.bend, id 14), the rewind entry
# (bend/ffi_job_rewind.bend, id 80) and the wait entry
# (bend/ffi_job_wait.bend, id 81), over requests and replies spelled here
# from the wire's primitives (bend/wire.bend), never the entries' own
# codecs: on every request Rust writes each answers the spelled decision;
# every other input gets exactly the error form with the entry's text.

# The job entry
# -------------

def job_spell_code(c: Jb.Code, rest: String) -> String:
  match c:
    case Jb.Code{hi, lo}:
      Wr.put_u32(hi, Wr.put_u32(lo, rest))

# an end: 0 an exit (its code), 1 the kill
def job_spell_end(e: Jb.End, rest: String) -> String:
  match e:
    case Jb.Exited{c}:
      Wr.put_nat(0n, job_spell_code(c, rest))
    case Jb.Killed{}:
      Wr.put_nat(1n, rest)

# a job: 0 live (kept, dropped), 1 ended (kept, dropped, the end)
def job_spell_job(j: Jb.J, rest: String) -> String:
  match j:
    case Jb.Live{k, d}:
      Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(d, rest)))
    case Jb.Ended{k, d, x}:
      Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(d, job_spell_end(x, rest))))

# an event: 0 output (its bytes), 1 an exit (its code), 2 the kill, 3 a tick
def job_spell_ev(e: Jb.JEv, rest: String) -> String:
  match e:
    case Jb.Out{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Jb.Quit{c}:
      Wr.put_nat(1n, job_spell_code(c, rest))
    case Jb.Kill{}:
      Wr.put_nat(2n, rest)
    case Jb.Tick{}:
      Wr.put_nat(3n, rest)

# the output cap: 0 the opt-out, 1 then the cap in bytes
def job_spell_cap(c: Maybe<&2, Nat>, rest: String) -> String:
  match c:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# the request Rust writes: the bound t, the cap, the job, the event
def job_spell_req(t: Nat, cap: Maybe<&2, Nat>, j: Jb.J, e: Jb.JEv) -> String:
  Wr.put_nat(t, job_spell_cap(cap, job_spell_job(j, job_spell_ev(e, ""))))

def job_spell_ends(es: List<&2, Jb.End>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case x <> t:
      job_spell_end(x, job_spell_ends(t, rest))

# the reply: the job after the event (`feed`), then the ends the event
# reported: their count, then each
def job_spell_answer(+t: Nat, +cap: Maybe<&2, Nat>, +j: Jb.J, +e: Jb.JEv) -> String:
  +es = Jb.ends.of(j, e)
  job_spell_job(Jb.feed(t, cap, j, e), Wr.put_nat(List.length(&2, Jb.End, es), job_spell_ends(es, "")))

# The laws' reader of a request, part by part (each part from the decode
# of the number that starts it)

def job_read_code.lo(+hi: U32, r: Wr.Dec<U32>) -> Wr.Dec<Jb.Code>:
  match r:
    case Wr.Got{lo, s}:
      Wr.Got{Jb.Code{hi, lo}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_code(r: Wr.Dec<U32>) -> Wr.Dec<Jb.Code>:
  match r:
    case Wr.Got{+hi, s}:
      job_read_code.lo(hi, Wr.get_u32(s))
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_end.code(r: Wr.Dec<Jb.Code>) -> Wr.Dec<Jb.End>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{Jb.Exited{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_end.tag(t: Nat, s: String) -> Wr.Dec<Jb.End>:
  match t:
    case 0n:
      job_read_end.code(job_read_code(Wr.get_u32(s)))
    case 1n:
      Wr.Got{Jb.Killed{}, s}
    case 2n+p:
      Wr.Bad{}

def job_read_end(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.End>:
  match r:
    case Wr.Got{t, s}:
      job_read_end.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_live.d(+k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{Jb.Live{k, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_live(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{+k, s}:
      job_read_live.d(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ended.x(+k: Nat, +d: Nat, r: Wr.Dec<Jb.End>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Jb.Ended{k, d, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ended.d(+k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{+d, s}:
      job_read_ended.x(k, d, job_read_end(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ended(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{+k, s}:
      job_read_ended.d(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_job.tag(t: Nat, s: String) -> Wr.Dec<Jb.J>:
  match t:
    case 0n:
      job_read_live(Wr.get_nat(s))
    case 1n:
      job_read_ended(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def job_read_job(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.J>:
  match r:
    case Wr.Got{t, s}:
      job_read_job.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ev.out(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.JEv>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Jb.Out{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ev.quit(r: Wr.Dec<Jb.Code>) -> Wr.Dec<Jb.JEv>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{Jb.Quit{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_ev.tag(t: Nat, s: String) -> Wr.Dec<Jb.JEv>:
  match t:
    case 0n:
      job_read_ev.out(Wr.get_nat(s))
    case 1n:
      job_read_ev.quit(job_read_code(Wr.get_u32(s)))
    case 2n:
      Wr.Got{Jb.Kill{}, s}
    case 3n:
      Wr.Got{Jb.Tick{}, s}
    case 4n+p:
      Wr.Bad{}

def job_read_ev(r: Wr.Dec<Nat>) -> Wr.Dec<Jb.JEv>:
  match r:
    case Wr.Got{t, s}:
      job_read_ev.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_cap.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def job_read_cap.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      job_read_cap.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def job_read_cap(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      job_read_cap.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def job_reads.ev(r: Wr.Dec<Jb.JEv>) -> Bool:
  match r:
    case Wr.Got{e, s}:
      Wr.end(s)
    case Wr.Bad{}:
      False{}

def job_reads.job(r: Wr.Dec<Jb.J>) -> Bool:
  match r:
    case Wr.Got{j, s}:
      job_reads.ev(job_read_ev(Wr.get_nat(s)))
    case Wr.Bad{}:
      False{}

def job_reads.cap(r: Wr.Dec<Maybe<&2, Nat>>) -> Bool:
  match r:
    case Wr.Got{c, s}:
      job_reads.job(job_read_job(Wr.get_nat(s)))
    case Wr.Bad{}:
      False{}

def job_reads.t(r: Wr.Dec<Nat>) -> Bool:
  match r:
    case Wr.Got{t, s}:
      job_reads.cap(job_read_cap(Wr.get_nat(s)))
    case Wr.Bad{}:
      False{}

# s is exactly one request: a bound, a cap, a job, an event, nothing after
def job_reads(s: String) -> Bool:
  job_reads.t(Wr.get_nat(s))

def job_why.end(whole: Bool) -> String:
  match whole:
    case True{}:
      ""
    case False{}:
      "job: input left over"

def job_why.ev(r: Wr.Dec<Jb.JEv>) -> String:
  match r:
    case Wr.Got{e, s}:
      job_why.end(Wr.end(s))
    case Wr.Bad{}:
      "job: bad event"

def job_why.job(r: Wr.Dec<Jb.J>) -> String:
  match r:
    case Wr.Got{j, s}:
      job_why.ev(job_read_ev(Wr.get_nat(s)))
    case Wr.Bad{}:
      "job: bad job"

def job_why.cap(r: Wr.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case Wr.Got{c, s}:
      job_why.job(job_read_job(Wr.get_nat(s)))
    case Wr.Bad{}:
      "job: bad cap"

def job_why.t(r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{t, s}:
      job_why.cap(job_read_cap(Wr.get_nat(s)))
    case Wr.Bad{}:
      "job: bad bound"

# why s is not one request: the first part of it that does not read, or
# input left over after a whole request
def job_why(s: String) -> String:
  job_why.t(Wr.get_nat(s))

# LAW job_entry_answers: on every request Rust writes (every number within the wire), the job entry answers the job after the event (`feed`: the step with the bytes kept plus dropped held to the bound) and the ends the event reported, as the laws spell them
law job_entry_answers:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(cap) == True{} : Bool}
  for hj: {wire_job_fits(j) == True{} : Bool}
  for he: {wire_ev_fits(e) == True{} : Bool}
  {FJb.ffi(job_spell_req(t, cap, j, e)) == job_spell_answer(t, cap, j, e) : String}

# LAW job_entry_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then the text that names the first part that does not read: "job: bad bound", "job: bad cap", "job: bad job", "job: bad event", or "job: input left over" (a whole request with more input after it)
law job_entry_malformed_exact:
  for +s: String
  for no: {job_reads(s) == False{} : Bool}
  {FJb.ffi(s) == SCon{'E', SCon{' ', job_why(s)}} : String}

# LAW job_entry_example: anchor: the strings Rust sends (with a bound of 100: Rust sends the wire's largest Nat, which the proven kernel cannot unfold; below the bound the answer does not depend on it, job_feed_fits) and the replies: output under a cap, output past it, an exit with code 7, a kill, a kill after the end; output that saturates a bound of 20; and one malformed input per error text (a U32 past 2^32 - 1 is not checked here: the checker builds it word by word, see wire_u32_exact)
law job_entry_example:
  {FJb.ffi("100,1,10,0,0,0,0,6,") == "0,6,0,0," : String} &
  {FJb.ffi("100,1,10,0,8,0,0,6,") == "0,10,4,0," : String} &
  {FJb.ffi("100,0,0,3,0,1,0,7,") == "1,3,0,0,0,7,1,0,0,7," : String} &
  {FJb.ffi("100,0,0,3,0,2,") == "1,3,0,1,1,1," : String} &
  {FJb.ffi("100,0,1,3,0,1,2,") == "1,3,0,1,0," : String} &
  {FJb.ffi("20,0,0,15,0,0,9,") == "0,20,0,0," : String} &
  {FJb.ffi("") == "E job: bad bound" : String} &
  {FJb.ffi("5,2,") == "E job: bad cap" : String} &
  {FJb.ffi("5,0,2,") == "E job: bad job" : String} &
  {FJb.ffi("5,0,0,1,1,4,") == "E job: bad event" : String} &
  {FJb.ffi("5,0,0,1,1,2,x") == "E job: input left over" : String}

# LAW job_req_fits_example: witness: a request of each kind of job and event fits the wire (job_entry_answers is not vacuous)
law job_req_fits_example:
  {LawsBase.wire_fits(5n) == True{} : Bool} & {LawsBase.wire_mfits(Some{10n}) == True{} : Bool} & {wire_job_fits(Jb.Live{1n, 2n}) == True{} : Bool} & {wire_job_fits(Jb.Ended{3n, 4n, Jb.Killed{}}) == True{} : Bool} & {wire_ev_fits(Jb.Out{6n}) == True{} : Bool} & {wire_ev_fits(Jb.Tick{}) == True{} : Bool}

# The rewind entry
# ----------------

# a commit, or none: 0 | 1, then the commit
def rw_spell_commit(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# a job: T|F it runs, then the commit it started after
def rw_spell_seen(s: Jb.Seen, rest: String) -> String:
  match s:
    case Jb.Seen{r, a}:
      Wr.put_bool(r, rw_spell_commit(a, rest))

def rw_spell_seens(js: List<&2, Jb.Seen>, rest: String) -> String:
  match js:
    case Nil{}:
      rest
    case s <> t:
      rw_spell_seen(s, rw_spell_seens(t, rest))

# the request Rust writes: the target entry's commit, the count of jobs,
# the jobs
def rw_spell_req(target: Maybe<&2, Nat>, +js: List<&2, Jb.Seen>) -> String:
  rw_spell_commit(target, Wr.put_nat(List.length(&2, Jb.Seen, js), rw_spell_seens(js, "")))

def rw_spell_bools(bs: List<&2, Bool>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case b <> t:
      Wr.put_bool(b, rw_spell_bools(t, rest))

# the reply: the count of kills, then T (send the kill) or F per job
def rw_spell_kills(+ks: List<&2, Bool>) -> String:
  Wr.put_nat(List.length(&2, Bool, ks), rw_spell_bools(ks, ""))

def rw_seens_fit(js: List<&2, Jb.Seen>) -> Bool:
  match js:
    case Nil{}:
      True{}
    case s <> t:
      match s:
        case Jb.Seen{r, a}:
          Bool.and(LawsBase.wire_mfits(a), rw_seens_fit(t))

# every number of the request fits the wire
def rw_req_fits(target: Maybe<&2, Nat>, +js: List<&2, Jb.Seen>) -> Bool:
  Bool.and(LawsBase.wire_mfits(target), Bool.and(LawsBase.wire_fits(List.length(&2, Jb.Seen, js)), rw_seens_fit(js)))

# the tree just after the entry committed at target holds the job that
# started after the commit `after`: with no target, none; else a job that
# started before any entry of the session, or after a commit below target
def rw_held_spec(target: Maybe<&2, Nat>, after: Maybe<&2, Nat>) -> Bool:
  match target after:
    case None{} None{}:
      False{}
    case None{} Some{a}:
      False{}
    case Some{t} None{}:
      True{}
    case Some{t} Some{a}:
      Bool.not(Nat.is_le(t, a))

# the kill a rewind sends a job: it runs and the tree does not hold it
def rw_kill_spec(target: Maybe<&2, Nat>, s: Jb.Seen) -> Bool:
  match s:
    case Jb.Seen{r, a}:
      match r:
        case True{}:
          Bool.not(rw_held_spec(target, a))
        case False{}:
          False{}

def rw_kills_spec(js: List<&2, Jb.Seen>, +target: Maybe<&2, Nat>) -> List<&2, Bool>:
  match js:
    case Nil{}:
      Nil{}
    case s <> t:
      rw_kill_spec(target, s) <> rw_kills_spec(t, target)

# the table as the model's slots: the job at place k of js has the id i + k
def rw_slots(js: List<&2, Jb.Seen>, +i: Nat) -> List<&2, Jb.Slot>:
  match js:
    case Nil{}:
      Nil{}
    case s <> t:
      match s:
        case Jb.Seen{r, a}:
          Jb.Slot{i, r} <> rw_slots(t, 1n+i)

def rw_put_if(b: Bool, x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

# the ids (from i) of the jobs of js the tree holds
def rw_held_ids(js: List<&2, Jb.Seen>, +target: Maybe<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match js:
    case Nil{}:
      Nil{}
    case s <> t:
      match s:
        case Jb.Seen{r, a}:
          rw_put_if(rw_held_spec(target, a), i, rw_held_ids(t, target, 1n+i))

def rw_stop_if(k: Bool, s: Jb.Slot) -> Jb.Slot:
  match k:
    case True{}:
      match s:
        case Jb.Slot{i, r}:
          Jb.Slot{i, False{}}
    case False{}:
      s

# the slots after the kills ks: a slot with a kill stops
def rw_stopped(ss: List<&2, Jb.Slot>, ks: List<&2, Bool>) -> List<&2, Jb.Slot>:
  match ss ks:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} k <> kr:
      Nil{}
    case s <> sr Nil{}:
      s <> sr
    case s <> sr k <> kr:
      rw_stop_if(k, s) <> rw_stopped(sr, kr)

# LAW job_rewind_exact: a rewind to the entry committed at target sends the kill exactly to each running job that the tree just after that entry does not hold, in order: with no target, to every running job; else to every running job that started after a commit at or past the target's (a job that started before any entry of the session is held); never to an ended job
law job_rewind_exact:
  for js: List<&2, Jb.Seen>
  for +target: Maybe<&2, Nat>
  {Jb.kills(js, target) == rw_kills_spec(js, target) : List<&2, Bool>}

# LAW job_rewind_refines: the kills are the model's rewind: with the jobs numbered by place, the slots after the kills are `rewind` of the slots to the tree that holds exactly the jobs that started before the target entry was committed
law job_rewind_refines:
  for +js: List<&2, Jb.Seen>
  for +target: Maybe<&2, Nat>
  {rw_stopped(rw_slots(js, 0n), Jb.kills(js, target)) == Jb.rewind(rw_slots(js, 0n), rw_held_ids(js, target, 0n)) : List<&2, Jb.Slot>}

# LAW job_rewind_stops_orphans: rewind_stops_orphans for what Rust runs: after the kills every running job is one the target tree holds
law job_rewind_stops_orphans:
  for +js: List<&2, Jb.Seen>
  for +target: Maybe<&2, Nat>
  {Jb.running_in(rw_stopped(rw_slots(js, 0n), Jb.kills(js, target)), rw_held_ids(js, target, 0n)) == True{} : Bool}

# LAW job_rewind_keeps_target_jobs: rewind_keeps_target_jobs for what Rust runs: the kills leave every job the target tree holds as it was
law job_rewind_keeps_target_jobs:
  for +js: List<&2, Jb.Seen>
  for +target: Maybe<&2, Nat>
  {Jb.kept(rw_stopped(rw_slots(js, 0n), Jb.kills(js, target)), rw_slots(js, 0n), rw_held_ids(js, target, 0n)) == True{} : Bool}

# The laws' reader of a rewind request, part by part

def rw_read_commit.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rw_read_commit.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      rw_read_commit.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def rw_read_commit(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      rw_read_commit.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def rw_read_seen.after(b: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Jb.Seen>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{Jb.Seen{b, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rw_read_seen(r: Wr.Dec<Bool>) -> Wr.Dec<Jb.Seen>:
  match r:
    case Wr.Got{b, s}:
      rw_read_seen.after(b, rw_read_commit(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def rw_read_seens.cons(x: Jb.Seen, r: Wr.Dec<List<&2, Jb.Seen>>) -> Wr.Dec<List<&2, Jb.Seen>>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{x <> xs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more jobs after the one cur answers
def rw_read_seens.go(n: Nat, cur: Wr.Dec<Jb.Seen>) -> Wr.Dec<List<&2, Jb.Seen>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          Wr.Got{[x], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{x, s}:
          rw_read_seens.cons(x, rw_read_seens.go(m, rw_read_seen(Wr.get_bool(s))))
        case Wr.Bad{}:
          Wr.Bad{}

def rw_read_seens(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Jb.Seen>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          rw_read_seens.go(m, rw_read_seen(Wr.get_bool(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def rw_reads.jobs(r: Wr.Dec<List<&2, Jb.Seen>>) -> Bool:
  match r:
    case Wr.Got{js, s}:
      Wr.end(s)
    case Wr.Bad{}:
      False{}

def rw_reads.target(r: Wr.Dec<Maybe<&2, Nat>>) -> Bool:
  match r:
    case Wr.Got{t, s}:
      rw_reads.jobs(rw_read_seens(Wr.get_nat(s)))
    case Wr.Bad{}:
      False{}

# s is exactly one rewind request: a target, the jobs, nothing after
def rw_reads(s: String) -> Bool:
  rw_reads.target(rw_read_commit(Wr.get_nat(s)))

# LAW job_rewind_entry_answers: on every request Rust writes (every number within the wire), the rewind entry answers one kill per job, in order, each as job_rewind_exact pins it
law job_rewind_entry_answers:
  for +target: Maybe<&2, Nat>
  for +js: List<&2, Jb.Seen>
  for +fits: {rw_req_fits(target, js) == True{} : Bool}
  {FJr.ffi(rw_spell_req(target, js)) == rw_spell_kills(rw_kills_spec(js, target)) : String}

# LAW job_rewind_entry_malformed_exact: every input that is not exactly one rewind request gets exactly the error form 'E ', then "job_rewind: malformed request"
law job_rewind_entry_malformed_exact:
  for +s: String
  for no: {rw_reads(s) == False{} : Bool}
  {FJr.ffi(s) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}

# LAW job_rewind_entry_example: anchor: the strings Rust sends and the replies: a target at commit 5 with jobs that started before any entry, after commit 4 and after commit 5; no target; an ended job and running jobs after commits 9, 4 and none; an empty table; and malformed inputs (a Maybe tag 2, input left over, nothing, fewer jobs than the count)
law job_rewind_entry_example:
  {FJr.ffi("1,5,3,T0,T1,4,T1,5,") == "3,FFT" : String} &
  {FJr.ffi("0,2,T0,F0,") == "2,TF" : String} &
  {FJr.ffi("1,5,4,F1,9,T1,9,T1,4,T0,") == "4,FTFF" : String} &
  {FJr.ffi("0,0,") == "0," : String} &
  {FJr.ffi("1,5,1,T2,") == "E job_rewind: malformed request" : String} &
  {FJr.ffi("0,1,T0,x") == "E job_rewind: malformed request" : String} &
  {FJr.ffi("") == "E job_rewind: malformed request" : String} &
  {FJr.ffi("0,2,T0,") == "E job_rewind: malformed request" : String}

# LAW job_rewind_req_fits_example: witness: a request with a target and jobs of each kind fits the wire (job_rewind_entry_answers is not vacuous)
law job_rewind_req_fits_example:
  {rw_req_fits(Some{5n}, [Jb.Seen{True{}, None{}}, Jb.Seen{False{}, Some{9n}}]) == True{} : Bool}

# LAW job_entries_malformed_witness: witness: inputs that are not one request exist for each entry (the malformed_exact laws are not vacuous)
law job_entries_malformed_witness:
  {job_reads("5,2,") == False{} : Bool} & {rw_reads("0,1,T0,x") == False{} : Bool} & {wt_reads("F") == False{} : Bool}

# The wait entry
# --------------

# the request Rust writes: T|F the deadline passed, T|F the end is ready
def wt_spell_req(due: Bool, ready: Bool) -> String:
  Wr.put_bool(due, Wr.put_bool(ready, ""))

# a turn: 0 the call waits, 1 it settles, 2 it detaches
def wt_spell_turn(t: Jb.Turn) -> String:
  match t:
    case Jb.Waits{}:
      Wr.put_nat(0n, "")
    case Jb.Settles{}:
      Wr.put_nat(1n, "")
    case Jb.Detaches{}:
      Wr.put_nat(2n, "")

# a poll: a passed deadline detaches, ready or not; else a ready end
# settles; else the call waits
def wt_poll_spec(due: Bool, ready: Bool) -> Jb.Turn:
  match due ready:
    case True{} True{}:
      Jb.Detaches{}
    case True{} False{}:
      Jb.Detaches{}
    case False{} True{}:
      Jb.Settles{}
    case False{} False{}:
      Jb.Waits{}

# the end an event brings, when it ends the job
def wt_end_of(e: Jb.JEv) -> Maybe<&2, Jb.End>:
  match e:
    case Jb.Out{n}:
      None{}
    case Jb.Quit{c}:
      Some{Jb.Exited{c}}
    case Jb.Kill{}:
      Some{Jb.Killed{}}
    case Jb.Tick{}:
      None{}

# the ticks of budget an event spends
def wt_ticks_of(e: Jb.JEv) -> Nat:
  match e:
    case Jb.Out{n}:
      0n
    case Jb.Quit{c}:
      0n
    case Jb.Kill{}:
      0n
    case Jb.Tick{}:
      1n

# what the call does on a turn: it detaches; it settles with the end the
# event brought; or it goes on to its answer after the event (next)
def wt_take(t: Jb.Turn, x: Maybe<&2, Jb.End>, next: Maybe<&2, Jb.Wait>) -> Maybe<&2, Jb.Wait>:
  match t:
    case Jb.Waits{}:
      next
    case Jb.Settles{}:
      match x:
        case None{}:
          None{}
        case Some{e}:
          Some{Jb.Settled{e}}
    case Jb.Detaches{}:
      Some{Jb.Detached{}}

# LAW job_wait_poll_exact: one poll of a blocking wait: a passed deadline detaches, even when the job's end is ready; else a ready end settles; else the call waits
law job_wait_poll_exact:
  for due: Bool
  for ready: Bool
  {Jb.poll(due, ready) == wt_poll_spec(due, ready) : Jb.Turn}

# LAW job_wait_polls_each_event: the blocking call (the model's `wait`) is the poll at each event: the deadline is due when no tick of budget is left, the end is ready when the event ends the job; on a wait it goes on after the event, with the event's ticks spent
law job_wait_polls_each_event:
  for +e: Jb.JEv
  for rest: List<&2, Jb.JEv>
  for +left: Nat
  {Jb.wait(e <> rest, left) == wt_take(Jb.poll(Nat.is_eq(left, 0n), Maybe.is_some(&2, Jb.End, wt_end_of(e))), wt_end_of(e), Jb.wait(rest, Nat.sub(left, wt_ticks_of(e)))) : Maybe<&2, Jb.Wait>}

# LAW job_wait_polls_at_rest: before any event the call is the poll with no end ready: it detaches when no tick of budget is left, else it waits (no answer yet)
law job_wait_polls_at_rest:
  for +left: Nat
  {Jb.wait(Nil{}, left) == wt_take(Jb.poll(Nat.is_eq(left, 0n), False{}), None{}, None{}) : Maybe<&2, Jb.Wait>}

def wt_reads.ready(r: Wr.Dec<Bool>) -> Bool:
  match r:
    case Wr.Got{x, s}:
      Wr.end(s)
    case Wr.Bad{}:
      False{}

def wt_reads.due(r: Wr.Dec<Bool>) -> Bool:
  match r:
    case Wr.Got{d, s}:
      wt_reads.ready(Wr.get_bool(s))
    case Wr.Bad{}:
      False{}

# s is exactly one poll request: two Bools, nothing after
def wt_reads(s: String) -> Bool:
  wt_reads.due(Wr.get_bool(s))

# LAW job_wait_entry_answers: on every request Rust writes the wait entry answers the turn job_wait_poll_exact pins
law job_wait_entry_answers:
  for due: Bool
  for ready: Bool
  {FJw.ffi(wt_spell_req(due, ready)) == wt_spell_turn(wt_poll_spec(due, ready)) : String}

# LAW job_wait_entry_malformed_exact: every input that is not exactly two Bools gets exactly the error form 'E ', then "job_wait: malformed request"
law job_wait_entry_malformed_exact:
  for +s: String
  for no: {wt_reads(s) == False{} : Bool}
  {FJw.ffi(s) == SCon{'E', SCon{' ', "job_wait: malformed request"}} : String}

# LAW job_wait_entry_example: anchor: the four strings Rust sends and their turns; malformed inputs (one Bool, input left over, nothing, a digit)
law job_wait_entry_example:
  {[FJw.ffi("TT"), FJw.ffi("TF"), FJw.ffi("FT"), FJw.ffi("FF")] == ["2,", "2,", "1,", "0,"] : List<&2, String>} &
  {[FJw.ffi("F"), FJw.ffi("TFT"), FJw.ffi(""), FJw.ffi("1,")] == ["E job_wait: malformed request", "E job_wait: malformed request", "E job_wait: malformed request", "E job_wait: malformed request"] : List<&2, String>}
