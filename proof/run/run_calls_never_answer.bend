# eukhe: the proof of LAW run_calls_never_answer

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

# a message with a tool call goes to the tools phase, whatever its text
def calls_never_answer(+cfg: RnState.Cfg, -text: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Ended.reply(RnState.Ended{text, True{}}), r, c, a, n, p) == RnState.St{RnState.Tools{}, r, c, a, n, p} : RnState.St}:
  {==}

def Run.run_calls_never_answer(cfg, text, r, c, a, n, p):
  calls_never_answer(cfg, text, r, c, a, n, p)
