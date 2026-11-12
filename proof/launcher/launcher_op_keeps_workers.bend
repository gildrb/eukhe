# eukhe: the proof of LAW launcher_op_keeps_workers
#
# `at` keeps the count (induction on i and the workers); a commit keeps
# the workers whatever it decides.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lok.at(~f: La.Wk -> La.Wk, i: Nat, ws: List<&2, La.Wk>) -> {List.length(&2, La.Wk, La.at(~f, i, ws)) == List.length(&2, La.Wk, ws) : Nat}:
  match i ws:
    case 0n Nil{}:
      {==}
    case 0n w <> t:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p w <> t:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, La.Wk, La.at(~f, p, t)), List.length(&2, La.Wk, t), lok.at(~f, p, t))

def lok.commit(b: Bool, +ws: List<&2, La.Wk>, a: Nat) -> {List.length(&2, La.Wk, Launcher.la_ws(La.commit.put(b, ws, a))) == List.length(&2, La.Wk, ws) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Launcher.launcher_op_keeps_workers(ws, a, op):
  match op:
    case La.Prompt{i}:
      lok.at(~La.prompt, i, ws)
    case La.Finish{i}:
      lok.at(~La.finish, i, ws)
    case La.Quiesce{i}:
      lok.at(~La.quiesce, i, ws)
    case La.Release{i}:
      lok.at(~La.release, i, ws)
    case La.Commit{}:
      lok.commit(La.all_closed(ws), ws, a)
