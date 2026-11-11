# eukhe: the laws of area stop, section cut: a reply cut at the output
# limit (R10 of laws/stop.bend), stated on the walk (bend/stop.bend), on
# the stop the entry reads from the facts Rust gathers (bend/ffi_stop.bend
# `facts`), and on the run's model (bend/run/step.bend,
# bend/run/request.bend), with the spec's window test
# (spec/harness/stop.bend S5) and the reply at a stop of laws/stop.bend
# (stop_reply)

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
# With no text it never stands. With text it stands exactly when it is
# not full (the window has room, or no compaction can run): the truncated
# reply is kept as the run's answer, whatever else its text holds; it
# answers the run once and the run sends no further request. With text
# and full, the run compacts (the overflow's compaction), then the
# request goes again.

# Spec helpers
# ------------

# R10: the reply the run reads at a cut reply with no tool call
# (generation.rs gathers the window's facts w, ca, pr, o, cu once, for the
# walk and for the ladder): the walk's pick at the stop the entry reads
# from them (FS.facts), then stop_reply with the same facts
def cut_reply(text: Bool, b: Bool, p: Bool, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, +cu: Bool, lo: Bool) -> RnState.Reply:
  +f = FS.facts(True{}, text, b, p, w, ca, pr, o, cu)
  LawsStop.stop_reply(S.walk(f), f, rc, k, row, w, ca, pr, o, cu, lo)

# Laws: a reply cut at the output limit (R10)
# -------------------------------------------
# The walk at a cut reply, then the reply the run reads at it from the
# facts Rust gathers (cut_reply): any window, catalog cap, prompt and
# output tokens, with or without a compaction to make, any recovery
# state, every live run at a reply.

# LAW stop_cut_empty_never_stands (R10): a cut reply with no text never
# stands, whatever else it holds, work pending or not, full or not:
# LengthStop continues it
# EXCLUDES: cut reasoning taken as the final answer; a cut reply with no
#   text kept because the window has room
law stop_cut_empty_never_stands:
  for b: Bool
  for p: Bool
  for fu: Bool
  {S.walk(S.Facts{True{}, False{}, b, p, fu}) == S.Goes{S.LengthStop{}} : S.Pick}

# LAW stop_cut_text_stands_unless_full (R10): a cut reply with text
# stands exactly when it is not full, whatever else it holds (markup the
# harness could not read too) and work pending or not: the truncated reply
# is kept; a full one is LengthStop's to continue
# EXCLUDES: a cut reply with text never taken as the answer (the user's
#   report: "the harness did not take the cut text as the answer"); one
#   kept at a full window; one refused for its markup, or continued by
#   MarkupStop
law stop_cut_text_stands_unless_full:
  for b: Bool
  for p: Bool
  {S.walk(S.Facts{True{}, True{}, b, p, False{}}) == S.Stands{} : S.Pick} &
  {S.walk(S.Facts{True{}, True{}, b, p, True{}}) == S.Goes{S.LengthStop{}} : S.Pick}

# LAW stop_cut_kept_answers_once (R10): at every reply of every live run,
# a cut reply with text whose window Rust found not full (the window has
# room, or no compaction can run) is the run's answer: the run is
# answered with its counts as they were and stays so whatever inputs
# follow, it counts exactly one answer, and the requests it sent, cut and
# will note stay exactly as they were
# EXCLUDES: a kept cut reply failed or retried with a note (the Cut note
#   and the error of the user's report), a second answer, a request after
#   it; a `full` the entry computes with another window test than the
#   spec's, so a reply with room is continued
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
  for room: {StSpec.full(w, ca, pr, o, cu) == False{} : Bool}
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

# LAW stop_cut_full_compacts (R10): at every reply of every live run that
# has its compaction left, a cut reply with text whose window Rust found
# full (it ran out, and a compaction can run) takes the run to the
# overflow's compaction, whatever the recovery state and the thinking
# levels: it spends the generation's one compaction and no note, retry or
# round (what a run does after a compaction: run_compact_is_the_rust_rule)
# EXCLUDES: a cut reply kept while the window is what ran out; a length
#   note where only a compaction makes room; a walk and a ladder that read
#   the window by different tests, so a reply the walk continues as full
#   gets a note, or fails the run
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
# 69000-token prompt, 4096 output tokens, below a 32768 catalog cap: not
# full) with text (the answer) and with no text (a noted retry); at a cut
# reply with text
# that ran into a 200000-token window (180000 + 15000 tokens) with a
# compaction to make (full: the cut overflow) and with none (the
# answer); whether each window is full
# EXCLUDES: vacuous premises (a window that is full, one that is not,
#   exist), a cut_reply that drifts from the shipped walk and ladder
law stop_cut_example:
  {[cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 262144n, 32768n, 69000n, 4096n, True{}, False{}), cut_reply(False{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 262144n, 32768n, 69000n, 4096n, True{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 200000n, 64000n, 180000n, 15000n, True{}, False{}), cut_reply(True{}, False{}, False{}, RnRecovery.RCfg{3n, 2n, 2n, 5n}, RnRecovery.Free{}, 0n, 200000n, 64000n, 180000n, 15000n, False{}, False{})] == [RnState.Plain{}, RnState.Error{False{}, True{}}, RnState.Overflow{True{}}, RnState.Plain{}] : List<&2, RnState.Reply>} &
  {[StSpec.full(262144n, 32768n, 69000n, 4096n, True{}), StSpec.full(200000n, 64000n, 180000n, 15000n, True{}), StSpec.full(200000n, 64000n, 180000n, 15000n, False{})] == [False{}, True{}, False{}] : List<&2, Bool>}
