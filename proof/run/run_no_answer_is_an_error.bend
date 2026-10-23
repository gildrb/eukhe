# eukhe: the proof of LAW run_no_answer_is_an_error

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

# a message that ends the model's turn with no text and no tool call steps
# as a noted error does: a retry with a note while notes are left, else
# the run fails on the model
def no_answer(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{False{}, False{}}), r, c, a, n, p) == Rn.note(cfg, r, c, a, n, p) : Rn.St}:
  {==}

def Run.run_no_answer_is_an_error(cfg, r, c, a, n, p):
  no_answer(cfg, r, c, a, n, p)
