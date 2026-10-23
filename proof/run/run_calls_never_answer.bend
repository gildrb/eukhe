# eukhe: the proof of LAW run_calls_never_answer

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

# a message with a tool call goes to the tools phase, whatever its text
def calls_never_answer(+cfg: Rn.Cfg, -text: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{text, True{}}), r, c, a, n, p) == Rn.St{Rn.Tools{}, r, c, a, n, p} : Rn.St}:
  {==}

def Run.run_calls_never_answer(cfg, text, r, c, a, n, p):
  calls_never_answer(cfg, text, r, c, a, n, p)
