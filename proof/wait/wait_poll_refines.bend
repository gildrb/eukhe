# eukhe: the proof of LAW wait_poll_refines
# Rust opens the stepper with a deadline of one tick or none; its first
# poll computes to the laws' table for each of the eight polls.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws

def wp.case(armed: Bool, a: Bool, c: Bool, l: Bool) -> {WaitLaws.ww_reply(FWt.step(WaitLaws.ww_opened(WaitLaws.ww_race_dl(armed)), WaitLaws.ww_spell(Wt.Polled{a, c, l}))) == WaitLaws.ww_spell_ends(WaitLaws.ww_prio(armed, Wt.Polled{a, c, l})) : String}:
  match armed a c l:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def WaitLaws.wait_poll_refines(armed, r):
  match r:
    case Wt.Polled{a, c, l}:
      wp.case(armed, a, c, l)
