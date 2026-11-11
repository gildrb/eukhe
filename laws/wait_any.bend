# eukhe: the laws of area wait_any

import Base
import ../bend/wait_any.bend as Wa
import ../bend/ffi_wait_any.bend as FWa
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/durable/wait_any.bend as WaSpec
import ../spec/durable/wait_any_wire.bend as SpW

# (H6) jobs.wait: the agent's one blocking wait on its own work
# -------------------------------------------------------------
# bend/wait_any.bend, run as the compiled core by bend/ffi_wait_any.bend
# (eukhe-bend rules/wait_any.rs; asked by eukhe-core durable/rlm/wait.rs
# at each poll of `jobs.wait`, and by durable/jobs at each change of a
# job's delivery). The requirement is spec/durable/wait_any.bend (S1-S5)
# and its wire spec/durable/wait_any_wire.bend (W1-W3); the laws state
# each as properties of the code's answers, never as a copy of it. Every
# input is free: any targets, cancel, cap, asked length, watchers, phase
# and events. (omp's source was not available to compare with; the Rust
# doc comments of rules/wait_any.rs and durable/jobs/delivery.rs state
# the same rules.)
#
# R1: a poll is the spec's (S1, S2): the first settled target, a refusal
#     with nothing to wait for, then the cancel, then the cap.
#     Laws: wait_any_takes_first_settled, wait_any_refuses_idle,
#     wait_any_open_ends.
# R2: a result goes to the notice only when no wait watches it and the
#     session has a wake path (S3).
#     Laws: wait_any_route_spec, wait_any_settle_places,
#     wait_any_unwatch_hands_on.
# R3: every wait has an exit: its length is the spec's (S4), never past
#     the cap.
#     Laws: wait_any_timeout_spec, wait_any_capped.
# R4: whatever waits watch, unwatch and take, a job's result is delivered
#     at most once (a notice or a wait, never both), each step as the
#     spec's (S5).
#     Laws: wait_any_once, wait_any_sent_never_delivers,
#     wait_any_step_counts_moves, wait_any_step_watchers,
#     wait_any_sent_final, wait_any_runs_until_settled,
#     wait_any_kept_until_taken (and R2's two placement laws).
# R5: the entry answers each request Rust writes (every Nat within the
#     wire) with the spelled model answer, and any other input with
#     `E wait_any: malformed request`.
#     Laws: wait_any_entry_answers, wait_any_entry_exact,
#     wait_any_entry_refuses.

# Spec helpers
# ------------

# the deliveries the code's steps make from d, counted on the laws' side:
# the sum of the deliveries every step answers (Wa.step is what the entry
# answers; the code's own counter Wa.deliveries is shipped nowhere)
def wa_count(es: List<&2, Wa.Ev>, +wake: Bool, d: Wa.D) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      +o = Wa.step(wake, d, e)
      Nat.add(WaSpec.out_k(o), wa_count(rest, wake, WaSpec.out_d(o)))

# R1: the poll
# ------------

# LAW wait_any_takes_first_settled (R1, S1): a poll over the targets pre,
# then t, then post, where t counts as settled (ready; gone only for a
# named wait: WaSpec.counts) and no target of pre does, ends taking t:
# its index is the length of pre, whatever the cancel and the cap say
# EXCLUDES: a later settled target taken before an earlier one, an index
#   off by one, a gone target taken by a wait-any (a result delivered
#   twice), a gone target skipped by a named wait, a cancel or the cap
#   winning over a settled target
law wait_any_takes_first_settled:
  for +named: Bool
  for cancel: Bool
  for late: Bool
  for +pre: List<&2, Wa.Tgt>
  for +t: Wa.Tgt
  for post: List<&2, Wa.Tgt>
  for none: {WaSpec.none_settled(named, pre) == True{} : Bool}
  for here: {WaSpec.counts(named, t) == True{} : Bool}
  {Wa.poll(named, cancel, late, List.append(&2, Wa.Tgt, pre, Con{t, post})) == Wa.Takes{List.length(&2, Wa.Tgt, pre)} : Wa.Pick}

# LAW wait_any_refuses_idle (R1, S2): a poll where no target counts as
# settled and none runs is refused (nothing to wait for), whatever the
# cancel and the cap say
# EXCLUDES: a wait with nothing running that waits for ever, a refusal
#   reported as a cancel or a cap
law wait_any_refuses_idle:
  for +named: Bool
  for cancel: Bool
  for late: Bool
  for +ts: List<&2, Wa.Tgt>
  for none: {WaSpec.none_settled(named, ts) == True{} : Bool}
  for idle: {WaSpec.some_runs(ts) == False{} : Bool}
  {Wa.poll(named, cancel, late, ts) == Wa.NoWork{} : Wa.Pick}

# LAW wait_any_open_ends (R1, S2): a poll where no target counts as
# settled and some target runs ends on the user's cancel (whether or not
# the cap passed), else on the cap, else waits on
# EXCLUDES: a refusal while work runs, the cap winning over the cancel, a
#   cancel or a passed cap ignored, a wait that ends with nothing to end it
law wait_any_open_ends:
  for +named: Bool
  for late: Bool
  for +ts: List<&2, Wa.Tgt>
  for none: {WaSpec.none_settled(named, ts) == True{} : Bool}
  for runs: {WaSpec.some_runs(ts) == True{} : Bool}
  {[Wa.poll(named, True{}, late, ts), Wa.poll(named, False{}, True{}, ts), Wa.poll(named, False{}, False{}, ts)] == [Wa.Stopped{}, Wa.Capped{}, Wa.Waits{}] : List<&2, Wa.Pick>}

# R2, R3: the route and the length
# --------------------------------

# LAW wait_any_route_spec (R2, S3): a result goes to the notice exactly
# when no wait watches it and the session has a wake path
# EXCLUDES: a watched result sent to the notice too (a double delivery), a
#   result dropped when the session has no wake path, an unwatched result
#   held while a wake path exists (a lost wake)
law wait_any_route_spec:
  for +watched: Bool
  for +wake: Bool
  {Wa.route(watched, wake) == WaSpec.route(watched, wake) : Wa.Route}

# LAW wait_any_timeout_spec (R3, S4): every wait lasts the spec's length
# EXCLUDES: the old 30 s budget as the cap, an asked length past the cap
#   kept, no length meaning for ever
law wait_any_timeout_spec:
  for +asked: Maybe<&2, Nat>
  {Wa.timeout(asked) == WaSpec.timeout(asked) : Nat}

# LAW wait_any_capped (R3): no wait lasts past the cap
# EXCLUDES: a wait without an exit
law wait_any_capped:
  for +asked: Maybe<&2, Nat>
  {Nat.is_le(Wa.timeout(asked), WaSpec.cap()) == True{} : Bool}

# R4: one job's delivery, step by step
# ------------------------------------

# LAW wait_any_step_watchers (R4, S5): from any phase and wake path, a
# watch adds one watcher, an unwatch removes one (none stays none), a
# settle and a take keep them
# EXCLUDES: a watcher count off by one, an unwatch below zero, a settle or
#   a take that drops the watchers (a watched result then sent to the
#   notice)
law wait_any_step_watchers:
  for +wake: Bool
  for +w: Nat
  for +p: Wa.Phase
  {[WaSpec.out_watchers(Wa.step(wake, Wa.D{w, p}, Wa.Watch{})), WaSpec.out_watchers(Wa.step(wake, Wa.D{1n+w, p}, Wa.Unwatch{})), WaSpec.out_watchers(Wa.step(wake, Wa.D{0n, p}, Wa.Unwatch{})), WaSpec.out_watchers(Wa.step(wake, Wa.D{w, p}, Wa.Settles{})), WaSpec.out_watchers(Wa.step(wake, Wa.D{w, p}, Wa.Taken{}))] == [1n+w, w, 0n, w, w] : List<&2, Nat>}

# LAW wait_any_step_counts_moves (R4, S5): every step answers one
# delivery exactly when it moves the result from not sent to sent, and
# none otherwise, from any state, event and wake path
# EXCLUDES: a delivery answered with no move (a double count), a move to
#   sent answered with none (a delivery Rust never sees), a kept result
#   counted as delivered
law wait_any_step_counts_moves:
  for +wake: Bool
  for +d: Wa.D
  for +e: Wa.Ev
  {WaSpec.out_k(Wa.step(wake, d, e)) == WaSpec.moved(WaSpec.d_phase(d), WaSpec.out_phase(Wa.step(wake, d, e))) : Nat}

# LAW wait_any_sent_final (R4, S5): a sent result stays sent after any
# event, with any watchers and wake path
# EXCLUDES: a sent result held again or reset to running (then delivered
#   a second time)
law wait_any_sent_final:
  for +wake: Bool
  for +w: Nat
  for +e: Wa.Ev
  {WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Sent{}}, e)) == Wa.Sent{} : Wa.Phase}

# LAW wait_any_runs_until_settled (R4, S5): while the job runs, a watch,
# an unwatch and a take leave it running: only its settle places a result
# EXCLUDES: a take of a running job that delivers nothing yet marks it
#   delivered, an unwatch that settles a running job
law wait_any_runs_until_settled:
  for +wake: Bool
  for +w: Nat
  {[WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Live{}}, Wa.Watch{})), WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Live{}}, Wa.Unwatch{})), WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Live{}}, Wa.Taken{}))] == [Wa.Live{}, Wa.Live{}, Wa.Live{}] : List<&2, Wa.Phase>}

# LAW wait_any_settle_places (R2, S3, S5): a running job that settles is
# kept for a wait when one or more waits watch it, whatever the wake
# path; with no watcher it goes to the notice (sent) when the session
# has a wake path, and is kept when it has none
# EXCLUDES: a watched result sent to the notice (the wait then takes it
#   too), an unwatched result held while a wake path exists (a lost
#   wake), a result sent with no wake path (dropped)
law wait_any_settle_places:
  for +wake: Bool
  for +w: Nat
  {[WaSpec.out_phase(Wa.step(wake, Wa.D{1n+w, Wa.Live{}}, Wa.Settles{})), WaSpec.out_phase(Wa.step(True{}, Wa.D{0n, Wa.Live{}}, Wa.Settles{})), WaSpec.out_phase(Wa.step(False{}, Wa.D{0n, Wa.Live{}}, Wa.Settles{}))] == [Wa.Kept{}, Wa.Sent{}, Wa.Kept{}] : List<&2, Wa.Phase>}

# LAW wait_any_kept_until_taken (R4, S5): a kept result is sent by a take,
# and stays kept through a watch or another settle
# EXCLUDES: a take of a kept result that leaves it kept (a second take
#   delivers it again), a second settle that re-places a kept result
law wait_any_kept_until_taken:
  for +wake: Bool
  for +w: Nat
  {[WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Kept{}}, Wa.Taken{})), WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Kept{}}, Wa.Watch{})), WaSpec.out_phase(Wa.step(wake, Wa.D{w, Wa.Kept{}}, Wa.Settles{}))] == [Wa.Sent{}, Wa.Kept{}, Wa.Kept{}] : List<&2, Wa.Phase>}

# LAW wait_any_unwatch_hands_on (R2, S3, S5): when a wait stops watching a
# kept result, it stays kept while another wait still watches it (two or
# more watchers before), whatever the wake path; when no watcher is left
# (one or none before) it goes to the notice (sent) when the session has
# a wake path, and stays kept when it has none
# EXCLUDES: the last watcher leaving without handing the result on (a
#   lost wake), a result sent to the notice while another wait still
#   watches it (a double delivery)
law wait_any_unwatch_hands_on:
  for +wake: Bool
  for +w: Nat
  {[WaSpec.out_phase(Wa.step(wake, Wa.D{2n+w, Wa.Kept{}}, Wa.Unwatch{})), WaSpec.out_phase(Wa.step(True{}, Wa.D{1n, Wa.Kept{}}, Wa.Unwatch{})), WaSpec.out_phase(Wa.step(True{}, Wa.D{0n, Wa.Kept{}}, Wa.Unwatch{})), WaSpec.out_phase(Wa.step(False{}, Wa.D{1n, Wa.Kept{}}, Wa.Unwatch{})), WaSpec.out_phase(Wa.step(False{}, Wa.D{0n, Wa.Kept{}}, Wa.Unwatch{}))] == [Wa.Kept{}, Wa.Sent{}, Wa.Sent{}, Wa.Kept{}, Wa.Kept{}] : List<&2, Wa.Phase>}

# LAW wait_any_once (R4): from any delivery state (any watchers, any
# phase), any events deliver the result at most once, counted on the
# laws' side as the sum of the deliveries each of the code's steps answers
# EXCLUDES: a result taken by a wait and also sent to the notice, a result
#   taken twice, a second settle delivered again, a held result sent again
#   when another wait stops watching
law wait_any_once:
  for +wake: Bool
  for +es: List<&2, Wa.Ev>
  for +d: Wa.D
  {Nat.is_le(wa_count(es, wake, d), 1n) == True{} : Bool}

# LAW wait_any_sent_never_delivers (R4): no event delivers a result that
# was already delivered
# EXCLUDES: a take, a settle or an unwatch of a sent result that delivers
#   it again
law wait_any_sent_never_delivers:
  for +wake: Bool
  for +w: Nat
  for +e: Wa.Ev
  {WaSpec.out_k(Wa.step(wake, Wa.D{w, Wa.Sent{}}, e)) == 0n : Nat}

# Anchors
# -------

# LAW wait_any_example (R1-R4): anchor: a wait-any takes the first ready
# target and skips a gone one; a named wait takes a gone one; with nothing
# running a wait is refused; a running wait is cancelled before it is
# capped; unwatched with a wake path a settle notifies, watched it is
# kept and the wait takes it; the last watcher leaving hands a kept result
# to the notice; the cap is 30 minutes
# EXCLUDES: a spec that drifts from the host's contract
law wait_any_example:
  {[Wa.poll(False{}, False{}, False{}, [Wa.Runs{}, Wa.Read{}, Wa.Unread{}]), Wa.poll(True{}, False{}, False{}, [Wa.Runs{}, Wa.Read{}]), Wa.poll(False{}, True{}, True{}, [Wa.Read{}]), Wa.poll(False{}, True{}, True{}, [Wa.Runs{}]), Wa.poll(False{}, False{}, True{}, [Wa.Runs{}]), Wa.poll(False{}, False{}, False{}, [Wa.Runs{}])] == [Wa.Takes{2n}, Wa.Takes{1n}, Wa.NoWork{}, Wa.Stopped{}, Wa.Capped{}, Wa.Waits{}] : List<&2, Wa.Pick>} &
  {[Wa.deliveries([Wa.Settles{}], True{}, Wa.fresh()), Wa.deliveries([Wa.Watch{}, Wa.Settles{}], True{}, Wa.fresh()), Wa.deliveries([Wa.Watch{}, Wa.Settles{}, Wa.Taken{}], True{}, Wa.fresh()), Wa.deliveries([Wa.Watch{}, Wa.Settles{}, Wa.Unwatch{}], True{}, Wa.fresh()), Wa.deliveries([Wa.Watch{}, Wa.Settles{}, Wa.Taken{}, Wa.Unwatch{}, Wa.Taken{}], True{}, Wa.fresh()), Wa.deliveries([Wa.Settles{}], False{}, Wa.fresh()), Wa.deliveries([Wa.Settles{}, Wa.Taken{}], False{}, Wa.fresh())] == [1n, 0n, 1n, 1n, 1n, 0n, 1n] : List<&2, Nat>} &
  {[Wa.timeout(None{}), Wa.timeout(Some{45n}), Wa.timeout(Some{3600n})] == [1800n, 45n, 1800n] : List<&2, Nat>}

# LAW wait_any_entry_example (R1-R3, R5): anchor: requests spelled by the
# grammar of crates/eukhe-bend/WIRE.md (the fields rules/wait_any.rs
# writes; no Rust test holds these strings) and the replies the entry
# answers, then two malformed inputs and an unknown question
# EXCLUDES: another spelling of a request or of a reply
law wait_any_entry_example:
  {[FWa.ffi("0,FFF2,0,1,"), FWa.ffi("0,FTF1,0,"), FWa.ffi("0,FFF0,"), FWa.ffi("0,TFF1,2,"), FWa.ffi("1,T0,0,2,"), FWa.ffi("1,T1,0,2,"), FWa.ffi("1,T1,1,1,"), FWa.ffi("1,F0,0,2,"), FWa.ffi("2,0,"), FWa.ffi("2,1,45,"), FWa.ffi("0,FFF2,1,3,"), FWa.ffi("2,0,x"), FWa.ffi("3,")] == ["1,1,", "4,", "2,", "1,0,", "0,2,1,", "1,1,0,", "0,2,1,", "0,1,0,", "1800,", "45,", Wr.err("wait_any: malformed request"), Wr.err("wait_any: malformed request"), Wr.err("wait_any: malformed request")] : List<&2, String>}

# LAW wait_any_delivery_example (R2, R4): anchor: a take of a sent result
# delivers nothing; a settle watched by two waits is kept for them; a
# settle then two takes, and a take after the watcher left, deliver once
# EXCLUDES: the double delivery and the two-watcher notice an adversary
#   found past the code's own counter
law wait_any_delivery_example:
  {[FWa.ffi("1,F0,2,3,"), FWa.ffi("1,T2,0,2,"), FWa.ffi("1,T2,1,1,"), FWa.ffi("1,T1,1,1,")] == ["0,2,0,", "2,1,0,", "1,1,0,", "0,2,1,"] : List<&2, String>} &
  {[wa_count([Wa.Settles{}, Wa.Taken{}, Wa.Taken{}], False{}, Wa.D{0n, Wa.Live{}}), wa_count([Wa.Watch{}, Wa.Settles{}, Wa.Taken{}, Wa.Unwatch{}, Wa.Taken{}], True{}, Wa.D{0n, Wa.Live{}}), wa_count([Wa.Watch{}, Wa.Watch{}, Wa.Settles{}], True{}, Wa.D{0n, Wa.Live{}})] == [1n, 1n, 0n] : List<&2, Nat>}

# R5: the entry
# -------------

# LAW wait_any_entry_answers (R5, W1-W2): a request spelled by the
# grammar, every Nat within the wire, is answered with the model's
# decision (pinned by the laws above), spelled by the grammar
# EXCLUDES: a field read into another, a code read as another, a default,
#   an answer spelled another way, an answer that is not the model's
law wait_any_entry_answers:
  for +q: FWa.Req
  for fit: {SpW.fit(q) == True{} : Bool}
  {FWa.ffi(SpW.w_req(q, "")) == SpW.w_reply(q) : String}

# LAW wait_any_entry_exact (R5, W3): every input the entry answers other
# than with the error form is a request spelled by the grammar, every Nat
# of it within the wire, with nothing after it
# EXCLUDES: an answer for input that is no request (an unknown question
#   or code, a malformed field, input left over), a guessed default
law wait_any_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FWa.ffi(s)) == False{} : Bool}
  exs q: FWa.Req
  {s == SpW.w_req(q, "") : String} & {SpW.fit(q) == True{} : Bool}

# LAW wait_any_entry_refuses (R5, W3): every error the entry answers is
# exactly `E wait_any: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law wait_any_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FWa.ffi(s)) == True{} : Bool}
  {FWa.ffi(s) == Wr.err("wait_any: malformed request") : String}

# LAW wait_any_entry_premises_witness (R5): a request that fits exists,
# input the entry refuses exists, and so does input it answers
# EXCLUDES: a vacuous entry law whose premise no input meets
law wait_any_entry_premises_witness:
  {[SpW.fit(FWa.QTimeout{None{}}), LawsBase.wire_opens_err(FWa.ffi("3,")), LawsBase.wire_opens_err(FWa.ffi("2,0,"))] == [True{}, True{}, False{}] : List<&2, Bool>}

# LAW wait_any_deliveries_spec (R4, S5): the code's count of deliveries
# is the spec's sum over every step
# EXCLUDES: a count that stops at the first delivery (a second delivery
#   unseen by wait_any_once)
law wait_any_deliveries_spec:
  for +es: List<&2, Wa.Ev>
  for +wake: Bool
  for +d: Wa.D
  {Wa.deliveries(es, wake, d) == WaSpec.deliveries(es, wake, d) : Nat}

# LAW wait_any_step_spec (R2, R4, S3, S5): every step of a job's delivery,
# from any watchers and phase, is the spec's: the watchers, the phase and
# the deliveries
# EXCLUDES: a sent result delivered again (a second take), a result
#   watched by two or more waits sent to the notice, a watcher count off by
#   one, a settle that ignores the wake path, a held result lost
law wait_any_step_spec:
  for +wake: Bool
  for +d: Wa.D
  for +e: Wa.Ev
  {Wa.step(wake, d, e) == WaSpec.step(wake, d, e) : Wa.Out}
