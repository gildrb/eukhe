# eukhe: the laws of area screen, section recover: the caps of the recoveries of a stuck
# model (H4.8, stated in laws/run/model.bend) over a row of the same stuck reply, on the
# model bend/run/recovery.bend

import Base
import ../../bend/run/recovery.bend as RnRecovery

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# The recoveries of bend/run/recovery.bend (Rec; requirement H4.8 of
# laws/run/model.bend, whose laws state each step): a length stop with its
# text cut (Long) and tool calls leaked as text that were not rebuilt
# (Leak{False, ..}) are retried with a note that counts that recovery's
# notes in a row, until its cap (RCfg.long, RCfg.leak) is reached; then
# the run fails. A Redo is a noted error, so its retry ends its request
# with a new note (H4.7). These laws follow a whole row of the same stuck
# reply on the model Rec.step, from any row j of that recovery's notes,
# under every configuration, the model's other fields (same, last) kept.
# A row that starts after no note or another recovery's note, and a cap
# of 0, are stated on the decision Rust calls (decide.recover) by
# laws/run/recover.bend: rec_length_notes_then_fails,
# rec_leak_notes_then_fails.

# the decisions on n replies o in a row, from the recoveries r, in order
def rec_row(+rc: RnRecovery.RCfg, +o: RnRecovery.Out, n: Nat, r: RnRecovery.Rec) -> List<&2, RnRecovery.Dec>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      +d = RnRecovery.Rec.step(rc, o, r)
      d <> rec_row(rc, o, m, RnRecovery.Dec.r(d))

# m retries whose notes of recovery k count j + 1, ..., j + m in a row, then
# the run's failure at the cap (the note stays the last one, j + m); same
# and last (the rounds of repeated calls) kept throughout
def rec_notes_then_quit(m: Nat, +k: RnRecovery.Rk, +j: Nat, +same: Nat, +last: Nat) -> List<&2, RnRecovery.Dec>:
  match m:
    case 0n:
      [RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{k, j, same, last}}]
    case 1n+p:
      RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{k, 1n+j, same, last}} <> rec_notes_then_quit(p, k, 1n+j, same, last)

# LAW rec_length_notes_then_quit (A2, H4.8): under a cap of j + m length notes
# (any leak, redirect and repeat caps), after a request whose note is
# length note j, m + 1 length stops in a row are retried m times, with
# length notes j + 1, ..., j + m, then the run fails at the cap: exactly the
# cap's notes in a row, counted one by one (same and last kept)
# EXCLUDES: a length row that never grows or restarts (length stops retried
#   forever), that grows by more than one a note, a cap reached early or
#   late, a retry after the cap, another note than a length note
law rec_length_notes_then_quit:
  for +lk: Nat
  for +rd: Nat
  for +rp: Nat
  for +j: Nat
  for +m: Nat
  for +same: Nat
  for +last: Nat
  {rec_row(RnRecovery.RCfg{Nat.add(m, j), lk, rd, rp}, RnRecovery.Long{}, 1n+m, RnRecovery.Rec{RnRecovery.Longs{}, j, same, last}) == rec_notes_then_quit(m, RnRecovery.Longs{}, j, same, last) : List<&2, RnRecovery.Dec>}

# LAW rec_leak_notes_then_quit (A2, H4.8): under a cap of j + m leak notes (any
# length, redirect and repeat caps), after a request whose note is leak note
# j, m + 1 replies in a row whose leaked calls were not rebuilt (any hash,
# any kept) are retried m times, with leak notes j + 1, ..., j + m, then the
# run fails at the cap: markup is never an answer
# EXCLUDES: a leak row that never grows or restarts (markup retried
#   forever), that grows by more than one a note, a cap reached early or
#   late, a retry after the cap, another note than a leak note
law rec_leak_notes_then_quit:
  for +lg: Nat
  for +rd: Nat
  for +rp: Nat
  for +h: Nat
  for +kept: Bool
  for +j: Nat
  for +m: Nat
  for +same: Nat
  for +last: Nat
  {rec_row(RnRecovery.RCfg{lg, Nat.add(m, j), rd, rp}, RnRecovery.Leak{False{}, h, kept}, 1n+m, RnRecovery.Rec{RnRecovery.Leaks{}, j, same, last}) == rec_notes_then_quit(m, RnRecovery.Leaks{}, j, same, last) : List<&2, RnRecovery.Dec>}
