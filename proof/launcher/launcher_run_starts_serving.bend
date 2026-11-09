# eukhe: the proof of LAW launcher_run_starts_serving
#
# The start state computes; its workers are `open` of bs, and the i-th
# of them is the i-th run, open (induction on bs and i together).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lrs.get(bs: List<&2, Bool>, i: Nat) -> {List.get(&2, La.Wk, La.open(bs), i) == Launcher.la_open_at(List.get(&2, Bool, bs, i)) : Maybe<&2, La.Wk>}:
  match bs i:
    case Nil{} _:
      {==}
    case b <> t 0n:
      {==}
    case b <> t 1n+p:
      lrs.get(t, p)

def Launcher.launcher_run_starts_serving(bs, i):
  ({==}, ({==}, lrs.get(bs, i)))
