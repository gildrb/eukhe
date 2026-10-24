# eukhe: the proof of LAW judge_refines

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../base/staging.bend as LStg

# the model removes the node of a judged entry exactly when its plan
# removes something, for either staleness
def jr.go(+i: Nat, c: Sg.Cand, l: Sg.Lock, a: Bool, probed: {Staging.sp_probed(c, l) == True{} : Bool}) -> {Sg.removes(Sg.Node{i, Staging.sp_sort(c), Staging.sp_held(l), a, True{}}) == Staging.sp_removes(Sg.judge.go(a, c, l)) : Bool}:
  match c:
    case Sg.CDir{}:
      match l:
        case Sg.LHeld{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
        case Sg.LFree{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
        case Sg.LAbsent{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Sg.CLock{}:
      match l:
        case Sg.LHeld{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
        case Sg.LFree{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
        case Sg.LAbsent{}:
          LStg.stg.absurdF({Sg.removes(Sg.Node{i, Staging.sp_sort(Sg.CLock{}), Staging.sp_held(Sg.LAbsent{}), a, True{}}) == Staging.sp_removes(Sg.judge.go(a, Sg.CLock{}, Sg.LAbsent{})) : Bool}, probed)

def Staging.judge_refines(i, c, l, now, own, inner, probed):
  %LA.rr.judge_old(c, l, now, own, inner) : {Sg.removes(Sg.Node{i, Staging.sp_sort(c), Staging.sp_held(l), Staging.sp_all_old(now, own <> inner), True{}}) == Staging.sp_removes(_) : Bool}
  jr.go(i, c, l, Staging.sp_all_old(now, own <> inner), probed)
