# eukhe: the proof of LAW launcher_stopped_is_final
#
# go over ops ++ more is go over more from go over ops (induction on ops);
# from a stopped state every step keeps the state (induction on more).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lsf.app(ops: List<&2, La.Op>, more: List<&2, La.Op>, +s: La.St) -> {La.go(List.append(&2, La.Op, ops, more), s) == La.go(more, La.go(ops, s)) : La.St}:
  match ops:
    case Nil{}:
      {==}
    case x <> t:
      lsf.app(t, more, La.step(s, x))

def lsf.stop(more: List<&2, La.Op>, +ws: List<&2, La.Wk>, +a: Nat) -> {La.go(more, La.St{ws, a, True{}}) == La.St{ws, a, True{}} : La.St}:
  match more:
    case Nil{}:
      {==}
    case x <> t:
      lsf.stop(t, ws, a)

def lsf.stopped(s: La.St, more: List<&2, La.Op>, e: {Launcher.la_stopped(s) == True{} : Bool}) -> {La.go(more, s) == s : La.St}:
  match s:
    case La.St{+ws, +a, d}:
      match d:
        case True{}:
          lsf.stop(more, ws, a)
        case False{}:
          LLa.la.absurd({La.go(more, La.St{ws, a, False{}}) == La.St{ws, a, False{}} : La.St}, e)

def lsf.main(+ops: List<&2, La.Op>, +more: List<&2, La.Op>, +s0: La.St, stopped: {Launcher.la_stopped(La.go(ops, s0)) == True{} : Bool}) -> {La.go(List.append(&2, La.Op, ops, more), s0) == La.go(ops, s0) : La.St}:
  Equal.trans(La.St, La.go(List.append(&2, La.Op, ops, more), s0), La.go(more, La.go(ops, s0)), La.go(ops, s0), lsf.app(ops, more, s0), lsf.stopped(La.go(ops, s0), more, stopped))

def Launcher.launcher_stopped_is_final(bs, ops, more, stopped):
  lsf.main(ops, more, La.St{La.open(bs), 0n, False{}}, stopped)
