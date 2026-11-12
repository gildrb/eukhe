# eukhe: the proof of LAW launcher_commit_waits_open_gate
#
# A worker with an open gate makes `all_closed` False (induction on the
# workers and j together), so the commit keeps the state.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

# a worker before workers that are not all closed
def lcw.and(w: La.Wk, -t: List<&2, La.Wk>, e: {La.all_closed(t) == False{} : Bool}) -> {La.all_closed(w <> t) == False{} : Bool}:
  match w:
    case La.Wk{x, c}:
      match c:
        case True{}:
          e
        case False{}:
          {==}

def lcw.open(ws: List<&2, La.Wk>, j: Nat, -b: Bool, at: {List.get(&2, La.Wk, ws, j) == Some{La.Wk{b, False{}}} : Maybe<&2, La.Wk>}) -> {La.all_closed(ws) == False{} : Bool}:
  match ws j:
    case Nil{} _:
      LLa.la.none_some(La.Wk, La.Wk{b, False{}}, {La.all_closed(Nil{}) == False{} : Bool}, at)
    case w <> t 0n:
      %Equal.sym(La.Wk, w, La.Wk{b, False{}}, LLa.la.some_inj(La.Wk, w, La.Wk{b, False{}}, at)) : {La.all_closed(_ <> t) == False{} : Bool}
      {==}
    case w <> t 1n+p:
      lcw.and(w, t, lcw.open(t, p, b, at))

def Launcher.launcher_commit_waits_open_gate(ws, a, j, b, at):
  %Equal.sym(Bool, La.all_closed(ws), False{}, lcw.open(ws, j, b, at)) : {La.commit.put(_, ws, a) == La.St{ws, a, False{}} : La.St}
  {==}
