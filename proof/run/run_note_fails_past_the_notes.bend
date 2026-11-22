# eukhe: the proof of LAW run_note_fails_past_the_notes
#
# PROOF: RnStep.note and RnStep.call compute on the notes left; a noted
# error reaches RnStep.note through RnStep.error, retryable or not.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# with a note left, the request is prepared again with one note fewer
def nf.more(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {RnStep.note(cfg, r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}:
  {==}

# with no note left, the run fails on the model
def nf.none(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat) -> {RnStep.note(cfg, r, c, a, 0n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, 0n, p} : RnState.St}:
  {==}

# a noted error past the notes, retryable or not, fails the run on the model
def nf.call(+cfg: RnState.Cfg, -retryable: Bool, +r: Nat, +c: Nat, +a: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Error{retryable, True{}}, r, c, a, 0n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, 0n, p} : RnState.St}:
  {==}

def Run.run_note_fails_past_the_notes(cfg, retryable, r, c, a, m, p):
  (nf.more(cfg, r, c, a, m, p), (nf.none(cfg, r, c, a, p), nf.call(cfg, retryable, r, c, a, p)))
