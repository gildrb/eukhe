# eukhe: the proof of LAW run_no_answer_is_an_error

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

# a message that ends the model's turn with no text and no tool call steps
# as a noted error does: a retry with a note while notes are left, else
# the run fails on the model
def no_answer(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Ended.reply(RnState.Ended{False{}, False{}}), r, c, a, n, p) == RnStep.note(cfg, r, c, a, n, p) : RnState.St}:
  {==}

def Run.run_no_answer_is_an_error(cfg, r, c, a, n, p):
  no_answer(cfg, r, c, a, n, p)
