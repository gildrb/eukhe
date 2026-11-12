# eukhe: the proof of LAW launcher_op_leaves_others
#
# `at` changes worker k alone (induction on k and the workers; at the
# same position, Nat.is_eq(k, k) would be True); the operation's worker is
# i (Some is injective); a commit is on no worker.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def loo.at(~f: La.Wk -> La.Wk, k: Nat, ws: List<&2, La.Wk>, j: Nat, ne: {Nat.is_eq(k, j) == False{} : Bool}) -> {List.get(&2, La.Wk, La.at(~f, k, ws), j) == List.get(&2, La.Wk, ws, j) : Maybe<&2, La.Wk>}:
  match k ws:
    case 0n Nil{}:
      {==}
    case 0n w <> t:
      match j:
        case 0n:
          LLa.la.absurd({List.get(&2, La.Wk, La.at(~f, 0n, w <> t), 0n) == List.get(&2, La.Wk, w <> t, 0n) : Maybe<&2, La.Wk>}, Equal.sym(Bool, True{}, False{}, ne))
        case 1n+q:
          {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p w <> t:
      match j:
        case 0n:
          {==}
        case 1n+q:
          loo.at(~f, p, t, q, ne)

# the operation's worker is i: k == i
def loo.on(-k: Nat, -i: Nat, +j: Nat, e: {Some{k} == Some{i} : Maybe<&2, Nat>}, other: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_eq(k, j) == False{} : Bool}:
  %Equal.sym(Nat, k, i, LLa.la.some_inj(Nat, k, i, e)) : {Nat.is_eq(_, j) == False{} : Bool}
  other

def Launcher.launcher_op_leaves_others(ws, a, op, i, j, on, other):
  match op:
    case La.Prompt{+k}:
      loo.at(~La.prompt, k, ws, j, loo.on(k, i, j, on, other))
    case La.Finish{+k}:
      loo.at(~La.finish, k, ws, j, loo.on(k, i, j, on, other))
    case La.Quiesce{+k}:
      loo.at(~La.quiesce, k, ws, j, loo.on(k, i, j, on, other))
    case La.Release{+k}:
      loo.at(~La.release, k, ws, j, loo.on(k, i, j, on, other))
    case La.Commit{}:
      LLa.la.none_some(Nat, i, {List.get(&2, La.Wk, Launcher.la_ws(La.step(La.St{ws, a, False{}}, La.Commit{})), j) == List.get(&2, La.Wk, ws, j) : Maybe<&2, La.Wk>}, on)
