# eukhe: the proof of LAW work_list_left_in_order
#
# PROOF: a hand-back names left exactly its open positions (LA.wlb.left).
# By induction on the items: the rest counted from 1 are the rest counted
# from 0, one up (LA.wlb.shift), and one up rises from 0, or from 1 after
# position 0, exactly when the rest rises from 0 (LA.wlb.rising_zero,
# LA.wlb.rising_up).

import Base
import ../../bend/work_list.bend as Wl
import ../../spec/agents/work_list.bend as S
import ../../laws/work_list.bend as WorkList
import ./base.bend as LA

def wli.rises(done: List<&2, Bool>) -> {S.rising(Wl.open(done, 0n), 0n) == True{} : Bool}:
  match done:
    case Nil{}:
      {==}
    case d <> +t:
      match d:
        case True{}:
          %wli.rises(t) : {S.rising(Wl.open(t, 1n), 0n) == _ : Bool}
          %LA.wlb.rising_zero(Wl.open(t, 0n)) : {S.rising(Wl.open(t, 1n), 0n) == _ : Bool}
          %LA.wlb.shift(t, 0n) : {S.rising(Wl.open(t, 1n), 0n) == S.rising(_, 0n) : Bool}
          {==}
        case False{}:
          %wli.rises(t) : {S.rising(Wl.open(t, 1n), 1n) == _ : Bool}
          %LA.wlb.rising_up(Wl.open(t, 0n), 0n) : {S.rising(Wl.open(t, 1n), 1n) == _ : Bool}
          %LA.wlb.shift(t, 0n) : {S.rising(Wl.open(t, 1n), 1n) == S.rising(_, 1n) : Bool}
          {==}

def WorkList.work_list_left_in_order(done):
  +o = Wl.open(done, 0n)
  %Equal.sym(List<&2, Nat>, S.left(Wl.of_open(o)), o, LA.wlb.left(o)) : {S.ascending(_) == True{} : Bool}
  wli.rises(done)
