# eukhe: the laws of area job

import Base
import ../bend/ffi_job.bend as FJb
import ../bend/ffi_job_rewind.bend as FJr
import ../bend/job.bend as Jb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S2) Jobs and limits
# --------------------
# the model in bend/job.bend. Every event is free:
# any output size, exit, kill or tick, in any order; any output cap or
# the opt-out; any budget; any job table. A tool call's journal: laws/tool_call.bend.
# The requirements below are read from this header, the comments of
# bend/job.bend, bend/ffi_job.bend, bend/ffi_job_rewind.bend and the Rust
# docs of JobState::step and JobTable::rewind_to
# (crates/eukhe-core/src/durable/jobs/mod.rs). oh-my-pi has no counterpart
# of this byte cap or of the rewind kills (its shell output spills to an
# artifact), so the Rust docs are the source. The laws of
# laws/job_step.bend belong to this area.
#
# A1: under the cap Some c a job keeps at most c bytes of its output and
#     counts the rest as dropped; every byte that fits under the cap is kept.
# A2: no byte is lost in silence: kept plus dropped is every byte the job
#     wrote before it ended.
# A3: the opt-out (None) keeps every byte.
# A4: an exit ends a live job as exited with exactly its code, a kill as
#     killed, both with the counts it had; the entry reports that one end.
# A5: an ended job stays as it ended: no later output, no second end.
# A6: output and ticks never end a job; a tick changes nothing.
# A7: Rust holds kept plus dropped to the wire bound t: below t the bound
#     changes nothing, output across t fills the counts to exactly t,
#     output is only ever cut, never invented, and a job past t takes none.
# A8: a blocking call answers once its budget of ticks passed, and when it
#     settles it reports the job's own end (the stepper: laws/job_wait.bend).
# A9: a rewind to a target entry stops every running job the target tree
#     does not hold and leaves every job it holds as it was; the tree holds
#     a job exactly when the job started before the target entry was
#     committed: a job that started before any entry of the session is
#     held by every target; with no target, or a target the table never
#     saw, no job is held.
# A10: the job entry answers, on every request Rust writes, the job after
#     the event (`feed`) and the ends the event reported (`ends.of`).
# A11: the job entry answers any other input with the error form naming
#     the first part that does not read: "job: bad bound", "job: bad cap",
#     "job: bad job", "job: bad event", or "job: input left over".
# A12: the rewind entry answers, on every request Rust writes, one kill
#     per job in order; any other input gets exactly the error form
#     "job_rewind: malformed request".

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

# LAW job_feed_fits: output that fits below t is the step: nothing is cut
law job_feed_fits:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}

# e2 is e itself or, when e is an output, an output of at most its bytes
def job_part(e2: Jb.JEv, e: Jb.JEv) -> Type:
  match e:
    case Jb.Out{n}:
      Sigma<&1, &1, Nat, m => {e2 == Jb.Out{m} : Jb.JEv} & {Nat.is_le(m, n) == True{} : Bool}>
    case Jb.Quit{c}:
      {e2 == Jb.Quit{c} : Jb.JEv}
    case Jb.Kill{}:
      {e2 == Jb.Kill{} : Jb.JEv}
    case Jb.Tick{}:
      {e2 == Jb.Tick{} : Jb.JEv}

# LAW job_feed_cuts_output (A7): from any job, every event the entry takes under the bound t is the
# step on a part of that event: an exit, a kill or a tick is stepped as itself, an output as an
# output of at most its bytes (which part: job_feed_fits, job_feed_fills, job_feed_past_bound)
# EXCLUDES: a bound that invents output bytes, turns an event into another kind, or changes an exit
#   code
law job_feed_cuts_output:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  exs e2: Jb.JEv
  job_part(e2, e) & {Jb.feed(t, cap, j, e) == Jb.step(cap, j, e2) : Jb.J}

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
# invents and reorders nothing. That Rust writes `put_req` is not proven
# here (the Rust codec is tested, not read by these laws).

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
# reported: their count, then each. What `feed` and `ends.of` answer is
# fixed by the job laws: job_feed_cuts_output, job_feed_fits,
# job_feed_fills, job_feed_past_bound and job_feed_bounded tie `feed` to
# `step`; the job_step laws (laws/job_step.bend) fix the step and
# `ends.of`
def job_spell_answer(+t: Nat, +cap: Maybe<&2, Nat>, +j: Jb.J, +e: Jb.JEv) -> String:
  +es = Jb.ends.of(j, e)
  job_spell_job(Jb.feed(t, cap, j, e), Wr.put_nat(List.length(&2, Jb.End, es), job_spell_ends(es, "")))

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

# LAW job_entry_bad_bound (A11): an input that does not start with a number within the wire (at most
# 14 digits, then ',') gets exactly the error form 'E job: bad bound'
# EXCLUDES: a default bound for garbage, another text, an answer for an empty input
law job_entry_bad_bound:
  for +s: String
  for no: @t: Nat -> @r: String -> {LawsBase.wire_fits(t) == True{} : Bool} -> {s == Wr.put_nat(t, r) : String} -> Empty
  {FJb.ffi(s) == Wr.err("job: bad bound") : String}

# LAW job_entry_bad_cap (A11): a bound within the wire followed by input that does not start with a
# cap (0, or 1 then a number within the wire) gets exactly the error form 'E job: bad cap'
# EXCLUDES: a cap tag past 1 read as a cap or the opt-out, a cap past the wire read, another text
law job_entry_bad_cap:
  for +t: Nat
  for +r: String
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for no: @c: Maybe<&2, Nat> -> @q: String -> {LawsBase.wire_mfits(c) == True{} : Bool} -> {r == job_spell_cap(c, q) : String} -> Empty
  {FJb.ffi(Wr.put_nat(t, r)) == Wr.err("job: bad cap") : String}

# LAW job_entry_bad_job (A11): a bound and a cap within the wire followed by input that does not
# start with a job (as job_spell_job spells it, every number within the wire) gets exactly the error
# form 'E job: bad job'
# EXCLUDES: a job tag past 1 or an end tag past 1 read as a job, another text
law job_entry_bad_job:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +r: String
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(cap) == True{} : Bool}
  for no: @j: Jb.J -> @q: String -> {wire_job_fits(j) == True{} : Bool} -> {r == job_spell_job(j, q) : String} -> Empty
  {FJb.ffi(Wr.put_nat(t, job_spell_cap(cap, r))) == Wr.err("job: bad job") : String}

# LAW job_entry_bad_event (A11): a bound, a cap and a job within the wire followed by input that does
# not start with an event (as job_spell_ev spells it, every number within the wire) gets exactly the
# error form 'E job: bad event'
# EXCLUDES: an event tag past 3 read as an event (a tick, a kill), another text
law job_entry_bad_event:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +r: String
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(cap) == True{} : Bool}
  for hj: {wire_job_fits(j) == True{} : Bool}
  for no: @e: Jb.JEv -> @q: String -> {wire_ev_fits(e) == True{} : Bool} -> {r == job_spell_ev(e, q) : String} -> Empty
  {FJb.ffi(Wr.put_nat(t, job_spell_cap(cap, job_spell_job(j, r)))) == Wr.err("job: bad event") : String}

# LAW job_entry_left_over (A11): a whole request within the wire followed by any more input gets
# exactly the error form 'E job: input left over', not an answer
# EXCLUDES: trailing garbage ignored (a request answered from a prefix), another text
law job_entry_left_over:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for +x: Char
  for +r: String
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(cap) == True{} : Bool}
  for hj: {wire_job_fits(j) == True{} : Bool}
  for he: {wire_ev_fits(e) == True{} : Bool}
  {FJb.ffi(Wr.put_nat(t, job_spell_cap(cap, job_spell_job(j, job_spell_ev(e, SCon{x, r}))))) == Wr.err("job: input left over") : String}

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

# LAW job_rewind_kills_per_job (A9, A12): the kills of a table are the kills of its parts, in order:
# the kills of two tables joined are the kills of the first, then those of the second (so one kill
# per job, each decided by that job alone)
# EXCLUDES: kills reordered, dropped, duplicated, or decided by another job of the table
law job_rewind_kills_per_job:
  for +xs: List<&2, Jb.Seen>
  for +ys: List<&2, Jb.Seen>
  for +target: Maybe<&2, Nat>
  {Jb.kills(List.append(&2, Jb.Seen, xs, ys), target) == List.append(&2, Bool, Jb.kills(xs, target), Jb.kills(ys, target)) : List<&2, Bool>}

# LAW job_rewind_spares_stopped (A9): a rewind to any target never sends the kill to a job that does
# not run
# EXCLUDES: a kill sent to an ended job (a second end reported)
law job_rewind_spares_stopped:
  for +a: Maybe<&2, Nat>
  for +target: Maybe<&2, Nat>
  {Jb.kills([Jb.Seen{False{}, a}], target) == [False{}] : List<&2, Bool>}

# LAW job_rewind_spares_presession (A9): a rewind to the entry committed at t keeps a running job that
# started before any entry of the session
# EXCLUDES: a rewind that kills the jobs every target tree holds
law job_rewind_spares_presession:
  for +t: Nat
  {Jb.kills([Jb.Seen{True{}, None{}}], Some{t}) == [False{}] : List<&2, Bool>}

# LAW job_rewind_spares_older (A9): a rewind to the entry committed at t keeps a running job that
# started after a commit a below t (before the target entry was committed)
# EXCLUDES: a job of the target tree killed (an off-by-one that kills a < t, a reversed order)
law job_rewind_spares_older:
  for +t: Nat
  for +a: Nat
  for before: {Nat.is_lt(a, t) == True{} : Bool}
  {Jb.kills([Jb.Seen{True{}, Some{a}}], Some{t}) == [False{}] : List<&2, Bool>}

# LAW job_rewind_kills_newer (A9): a rewind to the entry committed at t sends the kill to a running
# job that started after a commit a at or past t (the target entry itself included)
# EXCLUDES: an orphan job left running (an off-by-one that keeps a == t, a rewind that kills nothing)
law job_rewind_kills_newer:
  for +t: Nat
  for +a: Nat
  for after: {Nat.is_le(t, a) == True{} : Bool}
  {Jb.kills([Jb.Seen{True{}, Some{a}}], Some{t}) == [True{}] : List<&2, Bool>}

# LAW job_rewind_kills_without_target (A9): a rewind with no target (before every entry, or to an
# entry the table never saw) sends the kill to every running job, whenever it started
# EXCLUDES: a job kept by a rewind to before it started
law job_rewind_kills_without_target:
  for +a: Maybe<&2, Nat>
  {Jb.kills([Jb.Seen{True{}, a}], None{}) == [True{}] : List<&2, Bool>}

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

# LAW job_rewind_entry_answers (A12): on every request Rust writes (every number within the wire),
# the rewind entry answers the model's kills (`kills`, fixed by the job_rewind_kills_* and
# job_rewind_spares_* laws), one per job in order, as the laws spell them
law job_rewind_entry_answers:
  for +target: Maybe<&2, Nat>
  for +js: List<&2, Jb.Seen>
  for +fits: {rw_req_fits(target, js) == True{} : Bool}
  {FJr.ffi(rw_spell_req(target, js)) == rw_spell_kills(Jb.kills(js, target)) : String}

# LAW job_rewind_entry_exact (A12): every input the rewind entry does not answer with the error form
# is a request Rust writes: a target and a table of jobs, every number within the wire, nothing after
# EXCLUDES: an answer for input that is no request (a Maybe tag past 1, a bad Bool, fewer jobs than
#   the count, input left over)
law job_rewind_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FJr.ffi(s)) == False{} : Bool}
  exs target: Maybe<&2, Nat>
  exs js: List<&2, Jb.Seen>
  {rw_req_fits(target, js) == True{} : Bool} & {s == rw_spell_req(target, js) : String}

# LAW job_rewind_entry_refuses (A12): every error the rewind entry answers is exactly the error form
# 'E job_rewind: malformed request'
# EXCLUDES: an error text that varies with the input, a second error form
law job_rewind_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FJr.ffi(s)) == True{} : Bool}
  {FJr.ffi(s) == Wr.err("job_rewind: malformed request") : String}

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

# The wait's poll terms
# ---------------------
# Spelling and poll terms the wait laws (laws/job_wait.bend) read.

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
