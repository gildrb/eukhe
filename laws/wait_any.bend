# eukhe: the laws of area wait_any

import Base
import ../bend/wait_any.bend as Wa
import ../bend/ffi_wait_any.bend as FWa
import ../bend/wire.bend as Wr
import ../spec/durable/wait_any.bend as WaSpec

# (H6) jobs.wait: the agent's one blocking wait on its own work
# -------------------------------------------------------------
# bend/wait_any.bend, run as the compiled core by bend/ffi_wait_any.bend
# (eukhe-bend rules/wait_any.rs; asked by eukhe-core durable/rlm/wait.rs
# at each poll of `jobs.wait`, and by durable/jobs at each change of a
# job's delivery). The spec is spec/durable/wait_any.bend (S1-S4). Every
# input is free: any targets, cancel, cap, asked length, watchers, phase
# and events.
#
# R1: a poll is the spec's (S1, S2): the first settled target, a refusal
#     with nothing to wait for, then the cancel, then the cap.
# R2: a result goes to the notice only when no wait watches it and the
#     session has a wake path (S3).
# R3: every wait has an exit: its length is the spec's (S4), never past
#     the cap.
# R4: whatever waits watch, unwatch and take, a job's result is delivered
#     at most once (a notice or a wait, never both).

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
