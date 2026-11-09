# eukhe: the proof of LAW launcher_run_steps
#
# go is a left fold: induction on ops, from any state.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lrst.snoc(ops: List<&2, La.Op>, +s: La.St, +op: La.Op) -> {La.go(List.append(&2, La.Op, ops, [op]), s) == La.step(La.go(ops, s), op) : La.St}:
  match ops:
    case Nil{}:
      {==}
    case x <> t:
      lrst.snoc(t, La.step(s, x), op)

def Launcher.launcher_run_steps(bs, ops, op):
  lrst.snoc(ops, La.St{La.open(bs), 0n, False{}}, op)
