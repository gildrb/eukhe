# eukhe: the proof of LAW work_list_left_exactly_open
#
# PROOF: a hand-back names left exactly its open positions (LA.wlb.left).
# By induction on the items, then on k: a done item opens nothing at 0 and
# the rest counted from 1 are the rest counted from 0, one up
# (LA.wlb.shift): 0 is none of them (LA.wlb.member_zero) and k + 1 is one
# of them exactly when k is one of the rest's (LA.wlb.member_up); an item
# not done opens position 0 first.

import Base
import ../../bend/work_list.bend as Wl
import ../../spec/agents/work_list.bend as S
import ../../laws/work_list.bend as WorkList
import ./base.bend as LA

# k + 1 is among the rest counted from 1 exactly when the item after the
# first at k is open
def wlo.next(+t: List<&2, Bool>, +j: Nat, ih: {S.member(j, Wl.open(t, 0n)) == S.open_at(t, j) : Bool}) -> {S.member(1n+j, Wl.open(t, 1n)) == S.open_at(t, j) : Bool}:
  %ih : {S.member(1n+j, Wl.open(t, 1n)) == _ : Bool}
  %LA.wlb.member_up(j, Wl.open(t, 0n)) : {S.member(1n+j, Wl.open(t, 1n)) == _ : Bool}
  %LA.wlb.shift(t, 0n) : {S.member(1n+j, Wl.open(t, 1n)) == S.member(1n+j, _) : Bool}
  {==}

# position 0 is open exactly when the first item is not done
def wlo.zero(d: Bool, +t: List<&2, Bool>) -> {S.member(0n, Wl.open(d <> t, 0n)) == S.open_at(d <> t, 0n) : Bool}:
  match d:
    case True{}:
      %LA.wlb.member_zero(Wl.open(t, 0n)) : {S.member(0n, Wl.open(t, 1n)) == _ : Bool}
      %LA.wlb.shift(t, 0n) : {S.member(0n, Wl.open(t, 1n)) == S.member(0n, _) : Bool}
      {==}
    case False{}:
      {==}

# position j + 1 is open exactly when the item after the first at j is
def wlo.succ(d: Bool, +t: List<&2, Bool>, +j: Nat, ih: {S.member(j, Wl.open(t, 0n)) == S.open_at(t, j) : Bool}) -> {S.member(1n+j, Wl.open(d <> t, 0n)) == S.open_at(d <> t, 1n+j) : Bool}:
  match d:
    case True{}:
      wlo.next(t, j, ih)
    case False{}:
      wlo.next(t, j, ih)

def wlo.at(done: List<&2, Bool>, +k: Nat) -> {S.member(k, Wl.open(done, 0n)) == S.open_at(done, k) : Bool}:
  match done k:
    case Nil{} k:
      {==}
    case d <> +t 0n:
      wlo.zero(d, t)
    case d <> +t 1n+j:
      wlo.succ(d, t, j, wlo.at(t, j))

def WorkList.work_list_left_exactly_open(done, k):
  %wlo.at(done, k) : {S.member(k, S.left(Wl.outcome(done))) == _ : Bool}
  %LA.wlb.left(Wl.open(done, 0n)) : {S.member(k, S.left(Wl.outcome(done))) == S.member(k, _) : Bool}
  {==}
