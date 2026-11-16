# eukhe: the proof of LAW work_list_finished_exactly_all_done
#
# PROOF: the hand-back is finished exactly when its open positions are
# none (LA.wlb.finished). By induction on the items: none, then none are
# open; a done item opens nothing at 0 and the rest counted from 1 are the
# rest counted from 0, one up (LA.wlb.shift), which keeps emptiness
# (LA.wlb.nil_up); an item not done opens position 0.

import Base
import ../../bend/work_list.bend as Wl
import ../../spec/agents/work_list.bend as S
import ../../laws/work_list.bend as WorkList
import ./base.bend as LA

def wlf.none(done: List<&2, Bool>) -> {LA.wlb.nil(Wl.open(done, 0n)) == S.all_done(done) : Bool}:
  match done:
    case Nil{}:
      {==}
    case d <> +t:
      match d:
        case True{}:
          %wlf.none(t) : {LA.wlb.nil(Wl.open(t, 1n)) == _ : Bool}
          %LA.wlb.nil_up(Wl.open(t, 0n)) : {LA.wlb.nil(Wl.open(t, 1n)) == _ : Bool}
          %LA.wlb.shift(t, 0n) : {LA.wlb.nil(Wl.open(t, 1n)) == LA.wlb.nil(_) : Bool}
          {==}
        case False{}:
          {==}

def WorkList.work_list_finished_exactly_all_done(done):
  %wlf.none(done) : {S.finished(Wl.outcome(done)) == _ : Bool}
  LA.wlb.finished(Wl.open(done, 0n))
