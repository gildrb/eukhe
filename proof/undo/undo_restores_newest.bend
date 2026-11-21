# eukhe: the proof of LAW undo_restores_newest
#
# PROOF: the state after the history is the spec's (LA.unb.state); /undo on it answers the head of its live turns, refused when there is none (unu.act).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def unu.act(live: List<&2, Nat>, +m: Maybe<&2, Nat>) -> {Undo.sp_act(U.step(U.St{live, m}, U.Undo{})) == Undo.sp_undo(live) : U.Act}:
  match live:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def Undo.undo_restores_newest(h):
  %Equal.sym(U.St, Undo.sp_replay(h), U.St{Undo.sp_live(h, 0n), Undo.sp_first(h)}, LA.unb.state(h)) : {Undo.sp_act(U.step(_, U.Undo{})) == Undo.sp_undo(Undo.sp_live(h, 0n)) : U.Act}
  unu.act(Undo.sp_live(h, 0n), Undo.sp_first(h))
