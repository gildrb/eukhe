# eukhe: the laws of area stop, section cut: a reply cut at the output
# limit (R10 of laws/stop.bend), stated on the walk (bend/stop.bend), on
# the stop the entry reads from the facts Rust gathers (bend/ffi_stop.bend
# `facts`), and on the run's model (bend/run/step.bend,
# bend/run/request.bend), with the spec's window test
# (spec/harness/stop.bend S5, S7) and the reply at a stop of
# laws/stop.bend (stop_reply)

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/request.bend as RnRequest
import ../stop.bend as LawsStop
import ../../spec/harness/stop.bend as StSpec

# LAWS (R10 of laws/stop.bend): a reply cut at the output limit, as omp
# treats it (omp at c28b3e3,
# packages/coding-agent/src/session/session-maintenance.ts:3399-3534).
# With no text it never stands. With text it stands exactly when the
# window has room (not spent): the truncated reply is kept as the run's
# answer, whatever else its text holds; it answers the run once and the
# run sends no further request. With text and a spent window (an unknown
# window is spent: omp counts it so, :3412-3415), the run compacts (the
# overflow's compaction) when a compaction can run, then the request goes
# again; when none can, the reply is dropped (:3528-3533): the run ends
# with no further request (Rust keeps the reply in the transcript, out of
# the model's context, with no warning row).

# Spec helpers
# ------------

# R10: the reply the run reads at a cut reply with no tool call
# (generation.rs gathers the window's facts w, ca, pr, o, cu once, for the
# walk and for the ladder): the walk's pick at the stop the entry reads
# from them (FS.facts), then stop_reply with the same facts
def cut_reply(text: Bool, b: Bool, p: Bool, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, +cu: Bool, lo: Bool) -> RnState.Reply:
  +f = FS.facts(True{}, text, b, p, w, ca, pr, o, cu)
  LawsStop.stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo)

# R10: the pick keeps the reply as it is: the stop stands with it
def kept(p: S.Pick) -> Bool:
  match p:
    case S.Stands{}:
      True{}
    case S.Goes{d}:
      False{}
    case S.Drops{}:
      False{}

# Laws: a reply cut at the output limit (R10)
# -------------------------------------------
# The walk at a cut reply, then the reply the run reads at it from the
# facts Rust gathers (cut_reply): any window, catalog cap, prompt and
# output tokens, with or without a compaction to make, any recovery
# state, every live run at a reply.

# LAW stop_cut_empty_never_stands (R10): a cut reply with no text never
# stands, whatever else it holds, work pending or not, whatever the
# window: LengthStop continues it
# EXCLUDES: cut reasoning taken as the final answer, or dropped; a cut
#   reply with no text kept because the window has room
law stop_cut_empty_never_stands:
  for b: Bool
  for p: Bool
  for sp: Bool
  for cu: Bool
  {S.walk(S.Facts{True{}, False{}, b, p, sp, cu}) == S.Goes{S.LengthStop{}} : S.Pick}

# LAW stop_cut_text_stands_with_room (R10): a cut reply with text whose
# window has room (not spent) stands, whatever else it holds (markup the
# harness could not read too), work pending or not, with or without a
# compaction to make: the truncated reply is kept
# EXCLUDES: a cut reply with text never taken as the answer (the user's
#   report: "the harness did not take the cut text as the answer"); one
#   compacted or dropped while the window has room; one refused for its
#   markup, or continued by MarkupStop
law stop_cut_text_stands_with_room:
  for b: Bool
  for p: Bool
  for cu: Bool
  {S.walk(S.Facts{True{}, True{}, b, p, False{}, cu}) == S.Stands{} : S.Pick}

# LAW stop_cut_spent_never_kept (R10): a cut reply with text whose window
# is spent never stands with it, whatever else it holds and work pending
# or not: with a compaction to make LengthStop continues it (to the
# compaction), with none the reply is dropped (omp
# session-maintenance.ts:3528-3533: no recovery path, the turn leaves the
# active context and the run ends)
# EXCLUDES: a cut reply kept as the answer (with omp's warning) while the
#   window is what ran out and no compaction can run; one retried, failed
#   or compacted with no compaction to make; one dropped while a
#   compaction can run
law stop_cut_spent_never_kept:
  for b: Bool
  for p: Bool
  {S.walk(S.Facts{True{}, True{}, b, p, True{}, True{}}) == S.Goes{S.LengthStop{}} : S.Pick} &
  {S.walk(S.Facts{True{}, True{}, b, p, True{}, False{}}) == S.Drops{} : S.Pick}

# LAW stop_cut_unknown_window_never_kept (R10): at a cut reply whose
# window Rust does not know (0), the stop the entry reads never keeps the
# reply, whatever else it holds and whatever the catalog cap and the
# tokens: with text it goes to the compaction when one can run, else it
# is dropped (omp session-maintenance.ts:3412-3415: an unknown window is
# exhausted)
# EXCLUDES: a reply in an unknown window kept as the answer because the
#   window test needs a known window (the test before this change); one
#   retried with a length note where omp compacts
law stop_cut_unknown_window_never_kept:
  for t: Bool
  for b: Bool
  for p: Bool
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for cu: Bool
  {kept(S.walk(FS.facts(True{}, t, b, p, 0n, ca, pr, o, cu))) == False{} : Bool} &
  {S.walk(FS.facts(True{}, True{}, b, p, 0n, ca, pr, o, True{})) == S.Goes{S.LengthStop{}} : S.Pick} &
  {S.walk(FS.facts(True{}, True{}, b, p, 0n, ca, pr, o, False{})) == S.Drops{} : S.Pick}

# LAW stop_cut_kept_answers_once (R10): at every reply of every live run,
# a cut reply with text whose window Rust found with room (the spec's
# window test: not run out) is the run's answer: the run is answered with
# its counts as they were and stays so whatever inputs follow, it counts
# exactly one answer, and the requests it sent, cut and will note stay
# exactly as they were
# EXCLUDES: a kept cut reply failed or retried with a note (the Cut note
#   and the error of the user's report), a second answer, a request after
#   it; a window test in the entry other than the spec's, so a reply with
#   room is continued or dropped
law stop_cut_kept_answers_once:
  for +cfg: RnState.Cfg
  for b: Bool
  for p: Bool
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +cu: Bool
  for lo: Bool
  for room: {StSpec.ran_out(w, ca, pr, o) == False{} : Bool}
  for +fin: RnState.Fin
  for +got: RnState.Got
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +pl: Nat
  for +more: List<&2, RnState.Ev>
  for +t: RnRequest.Reqs
  {RnStep.run.go(RnState.Go{cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == RnState.St{RnState.Answered{}, r, c, a, n, pl} : RnState.St} &
  {LawsStop.answers.go(RnState.Go{cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == 1n : Nat} &
  {RnRequest.reqs.go(RnState.Go{cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}, t) == t : RnRequest.Reqs}

# LAW stop_cut_dropped_ends_the_run (R10): at every reply of every live
# run, a cut reply with text whose window Rust found run out (the spec's
# window test) with no compaction to make is dropped and ends the run: the
# run ends with its counts as they were and stays so whatever inputs
# follow, and the requests it sent, cut and will note stay exactly as
# they were (omp session-maintenance.ts:3528-3533 returns with no
# continuation, no retry and no notice)
# EXCLUDES: a dropped reply retried with a length note, failed with an
#   error, or followed by a request; a kept reply where the window ran
#   out; a window test in the entry other than the spec's
law stop_cut_dropped_ends_the_run:
  for +cfg: RnState.Cfg
  for b: Bool
  for p: Bool
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for lo: Bool
  for spent: {StSpec.ran_out(w, ca, pr, o) == True{} : Bool}
  for +fin: RnState.Fin
  for +got: RnState.Got
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +pl: Nat
  for +more: List<&2, RnState.Ev>
  for +t: RnRequest.Reqs
  {S.walk(FS.facts(True{}, True{}, b, p, w, ca, pr, o, False{})) == S.Drops{} : S.Pick} &
  {RnStep.run.go(RnState.Go{cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, False{}, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == RnState.St{RnState.Answered{}, r, c, a, n, pl} : RnState.St} &
  {RnRequest.reqs.go(RnState.Go{cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, False{}, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}, t) == t : RnRequest.Reqs}

# LAW stop_cut_full_compacts (R10): at every reply of every live run that
# has its compaction left, a cut reply with text whose window Rust found
# full (it ran out, and a compaction can run) takes the run to the
# overflow's compaction, whatever the recovery state and the thinking
# levels: it spends the generation's one compaction and no note, retry or
# round (what a run does after a compaction: run_compact_is_the_rust_rule)
# EXCLUDES: a cut reply kept or dropped while a compaction can make room;
#   a length note where only a compaction makes room; a walk and a ladder
#   that read the window by different tests, so a reply the walk continues
#   as full gets a note, or fails the run
law stop_cut_full_compacts:
  for +cfg: RnState.Cfg
  for b: Bool
  for p: Bool
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +w: Nat
  for +ca: Nat
  for +pr: Nat
  for +o: Nat
  for +cu: Bool
  for lo: Bool
  for full: {StSpec.full(w, ca, pr, o, cu) == True{} : Bool}
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +pl: Nat
  {RnStep.call(cfg, cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, cu, lo), r, 1n+c, a, n, pl) == RnState.St{RnState.Compact{True{}}, r, c, a, n, pl} : RnState.St}

# LAW stop_cut_example (R10): anchor and witness: the replies the run
# reads at a cut reply like the user's (a 262144-token window, a
# 69000-token prompt, 4096 output tokens, below a 32768 catalog cap: room)
# with text (the answer) and with no text (a noted retry); at a cut reply
# with text that ran into a 200000-token window (180000 + 15000 tokens)
# with a compaction to make (the cut overflow) and with none (dropped: the
# run ends); at a cut reply with text in an unknown window with a
# compaction to make (the cut overflow) and with none (dropped); the
# walk's pick at each window with text; whether each window ran out
# EXCLUDES: vacuous premises (a window that ran out, one with room,
#   exist), a cut_reply that drifts from the shipped walk and ladder
law stop_cut_example:
  {[cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 262144n, 32768n, 69000n, 4096n, True{}, False{}), cut_reply(False{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 262144n, 32768n, 69000n, 4096n, True{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 200000n, 64000n, 180000n, 15000n, True{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 200000n, 64000n, 180000n, 15000n, False{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 0n, 32768n, 69000n, 4096n, True{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 0n, 32768n, 69000n, 4096n, False{}, False{})] == [RnState.Plain{}, RnState.Error{False{}, True{}}, RnState.Overflow{True{}}, RnState.Plain{}, RnState.Overflow{True{}}, RnState.Plain{}] : List<&2, RnState.Reply>} &
  {[S.walk(FS.facts(True{}, True{}, False{}, False{}, 262144n, 32768n, 69000n, 4096n, True{})), S.walk(FS.facts(True{}, True{}, False{}, False{}, 200000n, 64000n, 180000n, 15000n, True{})), S.walk(FS.facts(True{}, True{}, False{}, False{}, 200000n, 64000n, 180000n, 15000n, False{})), S.walk(FS.facts(True{}, True{}, False{}, False{}, 0n, 32768n, 69000n, 4096n, True{})), S.walk(FS.facts(True{}, True{}, False{}, False{}, 0n, 32768n, 69000n, 4096n, False{}))] == [S.Stands{}, S.Goes{S.LengthStop{}}, S.Drops{}, S.Goes{S.LengthStop{}}, S.Drops{}] : List<&2, S.Pick>} &
  {[StSpec.ran_out(262144n, 32768n, 69000n, 4096n), StSpec.ran_out(200000n, 64000n, 180000n, 15000n), StSpec.ran_out(0n, 32768n, 69000n, 4096n)] == [False{}, True{}, True{}] : List<&2, Bool>}
