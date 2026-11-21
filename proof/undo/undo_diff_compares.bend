# eukhe: the proof of LAW undo_diff_compares
#
# PROOF: the state after the history is the spec's (LA.unb.state); /diff of the turn answers the head of its live turns (und.turn), /diff all its first turn (und.all).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def und.turn(live: List<&2, Nat>, +m: Maybe<&2, Nat>) -> {Undo.sp_act(U.step(U.St{live, m}, U.Diff{U.Turn{}})) == Undo.sp_cmp(Undo.sp_head(live)) : U.Act}:
  match live:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def und.all(+live: List<&2, Nat>, m: Maybe<&2, Nat>) -> {Undo.sp_act(U.step(U.St{live, m}, U.Diff{U.All{}})) == Undo.sp_cmp(m) : U.Act}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def Undo.undo_diff_compares(h):
  +l = Undo.sp_live(h, 0n)
  +f = Undo.sp_first(h)
  +e = Equal.sym(U.St, Undo.sp_replay(h), U.St{l, f}, LA.unb.state(h))
  +a = und.turn(l, f)
  +b = und.all(l, f)
  +a2 = Equal.trans(U.Act, Undo.sp_act(U.step(Undo.sp_replay(h), U.Diff{U.Turn{}})), Undo.sp_act(U.step(U.St{l, f}, U.Diff{U.Turn{}})), Undo.sp_cmp(Undo.sp_head(l)), Equal.cong(U.St, U.Act, z => Undo.sp_act(U.step(z, U.Diff{U.Turn{}})), Undo.sp_replay(h), U.St{l, f}, Equal.sym(U.St, U.St{l, f}, Undo.sp_replay(h), e)), a)
  +b2 = Equal.trans(U.Act, Undo.sp_act(U.step(Undo.sp_replay(h), U.Diff{U.All{}})), Undo.sp_act(U.step(U.St{l, f}, U.Diff{U.All{}})), Undo.sp_cmp(f), Equal.cong(U.St, U.Act, z => Undo.sp_act(U.step(z, U.Diff{U.All{}})), Undo.sp_replay(h), U.St{l, f}, Equal.sym(U.St, U.St{l, f}, Undo.sp_replay(h), e)), b)
  (a2, b2)
