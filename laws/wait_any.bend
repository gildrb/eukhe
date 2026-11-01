# eukhe: the laws of area wait_any

import Base
import ../bend/wait_any.bend as Wa
import ../bend/ffi_wait_any.bend as FWa
import ../bend/wire.bend as Wr
import ../spec/durable/wait_any.bend as WaSpec
import ../spec/durable/wait_any_wire.bend as SpW

# (H6) jobs.wait: the agent's one blocking wait on its own work
# -------------------------------------------------------------
# bend/wait_any.bend, run as the compiled core by bend/ffi_wait_any.bend
# (eukhe-bend rules/wait_any.rs; asked by eukhe-core durable/rlm/wait.rs
# at each poll of `jobs.wait`, and by durable/jobs at each change of a
# job's delivery). The spec is spec/durable/wait_any.bend (S1-S5), its
# wire spec/durable/wait_any_wire.bend (W1-W3). Every input is free: any
# targets, cancel, cap, asked length, watchers, phase and events.
#
# R1: a poll is the spec's (S1, S2): the first settled target, a refusal
#     with nothing to wait for, then the cancel, then the cap.
# R2: a result goes to the notice only when no wait watches it and the
#     session has a wake path (S3).
# R3: every wait has an exit: its length is the spec's (S4), never past
#     the cap.
# R4: whatever waits watch, unwatch and take, a job's result is delivered
#     at most once (a notice or a wait, never both), each step as the
#     spec's (S5).
# R5: the entry answers each request Rust writes (every Nat within the
#     wire) with the spelled spec answer, and any other input with
#     `E wait_any: malformed request`.

# Spec helpers
# ------------

# the deliveries the code's own steps make from d, counted on the laws'
# side: the sum of the deliveries every step answers (the code's counter,
# Wa.deliveries, is not what measures R4)
def wa_count(es: List<&2, Wa.Ev>, +wake: Bool, d: Wa.D) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      +o = Wa.step(wake, d, e)
      Nat.add(WaSpec.out_k(o), wa_count(rest, wake, WaSpec.out_d(o)))

# LAW wait_any_poll_spec (R1, S1, S2): every poll is the spec's
# EXCLUDES: a later settled target taken before an earlier one, a gone
#   target taken by a wait-any (a result delivered twice), a gone target
#   refused to a named wait, a refusal while work runs, a cancel or the cap
#   winning over a settled target, the cap winning over the cancel, a wait
#   with nothing running that waits for ever
law wait_any_poll_spec:
  for +named: Bool
  for +cancel: Bool
  for +late: Bool
  for +ts: List<&2, Wa.Tgt>
  {Wa.poll(named, cancel, late, ts) == WaSpec.poll(named, cancel, late, ts) : Wa.Pick}

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

# LAW wait_any_settle_routes (R2): a running job that settles goes where
# the spec's route sends it, watched when any wait watches it
# EXCLUDES: a settle that ignores its watchers or the wake path
law wait_any_settle_routes:
  for +w: Nat
  for +wake: Bool
  {Wa.step(wake, Wa.D{w, Wa.Live{}}, Wa.Settles{}) == Wa.deliver(WaSpec.route(Wa.watched(w), wake), w) : Wa.Out}

# LAW wait_any_once (R4): from a fresh job, any events deliver its result
# at most once
# EXCLUDES: a result taken by a wait and also sent to the notice, a result
#   taken twice, a second settle delivered again, a held result sent again
#   when another wait stops watching
law wait_any_once:
  for +wake: Bool
  for +es: List<&2, Wa.Ev>
  {Nat.is_le(Wa.deliveries(es, wake, Wa.fresh()), 1n) == True{} : Bool}

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

# LAW wait_any_watched_spec (R2, S5): a job is watched exactly when it has
# a watcher
# EXCLUDES: only one watcher counted as watching (two waits' result sent
#   to the notice)
law wait_any_watched_spec:
  for +w: Nat
  {Wa.watched(w) == WaSpec.watching(w) : Bool}

# LAW wait_any_deliver_spec (R2, S5): a placed result is the spec's: sent
# with one delivery to the notice, kept with none for a wait
# EXCLUDES: a notice that counts no delivery, a kept result counted as
#   delivered, the watchers changed
law wait_any_deliver_spec:
  for +r: Wa.Route
  for +w: Nat
  {Wa.deliver(r, w) == WaSpec.deliver(r, w) : Wa.Out}

# LAW wait_any_fresh_spec (R4): a job starts running with no watcher
# EXCLUDES: a fresh job already settled or sent (wait_any_once vacuous)
law wait_any_fresh_spec:
  {Wa.fresh() == WaSpec.fresh() : Wa.D}

# LAW wait_any_deliveries_spec (R4, S5): the code's count of deliveries
# is the spec's sum over every step
# EXCLUDES: a count that stops at the first delivery (a second delivery
#   unseen by wait_any_once)
law wait_any_deliveries_spec:
  for +es: List<&2, Wa.Ev>
  for +wake: Bool
  for +d: Wa.D
  {Wa.deliveries(es, wake, d) == WaSpec.deliveries(es, wake, d) : Nat}

# LAW wait_any_once_counted (R4): from a fresh job, the code's own steps,
# counted on the laws' side, deliver its result at most once
# EXCLUDES: a result taken twice, a result taken and sent to the notice,
#   however the code counts its deliveries
law wait_any_once_counted:
  for +wake: Bool
  for +es: List<&2, Wa.Ev>
  {Nat.is_le(wa_count(es, wake, WaSpec.fresh()), 1n) == True{} : Bool}

# LAW wait_any_sent_never_delivers (R4): no event delivers a result that
# was already delivered
# EXCLUDES: a take, a settle or an unwatch of a sent result that delivers
#   it again
law wait_any_sent_never_delivers:
  for +wake: Bool
  for +w: Nat
  for +e: Wa.Ev
  {WaSpec.out_k(Wa.step(wake, Wa.D{w, Wa.Sent{}}, e)) == 0n : Nat}

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

# LAW wait_any_entry_example (R1-R3): anchor: the wire strings Rust sends
# and the replies it reads
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
  {[wa_count([Wa.Settles{}, Wa.Taken{}, Wa.Taken{}], False{}, WaSpec.fresh()), wa_count([Wa.Watch{}, Wa.Settles{}, Wa.Taken{}, Wa.Unwatch{}, Wa.Taken{}], True{}, WaSpec.fresh()), wa_count([Wa.Watch{}, Wa.Watch{}, Wa.Settles{}], True{}, WaSpec.fresh())] == [1n, 1n, 0n] : List<&2, Nat>}

# LAW wait_any_entry_answers (R5, W1-W2): a request spelled by the
# grammar, every Nat within the wire, is answered with the spelled spec
# answer
# EXCLUDES: a field read into another, a code read as another, a default,
#   an answer spelled another way, a step reply that is not the spec's
law wait_any_entry_answers:
  for +q: FWa.Req
  for fit: {SpW.fit(q) == True{} : Bool}
  {FWa.ffi(SpW.w_req(q, "")) == SpW.w_reply(q) : String}

# LAW wait_any_entry_reads (R5, W1): the laws' reader reads every spelled
# request that fits back whole
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law wait_any_entry_reads:
  for +q: FWa.Req
  for fit: {SpW.fit(q) == True{} : Bool}
  {SpW.read_req(SpW.w_req(q, "")) == Some{q} : Maybe<&2, FWa.Req>}

# LAW wait_any_entry_malformed_exact (R5, W3): input that is no whole
# request answers the error form
# EXCLUDES: a malformed request read as a default, trailing input
#   ignored, another error text
law wait_any_entry_malformed_exact:
  for +s: String
  for no: {SpW.read_req(s) == None{} : Maybe<&2, FWa.Req>}
  {FWa.ffi(s) == Wr.err("wait_any: malformed request") : String}

# LAW wait_any_entry_premises_witness (R5): a request that fits exists,
# and so does input that is no request
# EXCLUDES: a vacuous entry law whose premise no input meets
law wait_any_entry_premises_witness:
  {(SpW.fit(FWa.QTimeout{None{}}), SpW.read_req("3,")) == (True{}, None{}) : Bool & Maybe<&2, FWa.Req>}
