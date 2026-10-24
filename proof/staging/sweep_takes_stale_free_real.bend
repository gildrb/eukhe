# eukhe: the proof of LAW sweep_takes_stale_free_real

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

# a stale judged entry gets the plan of its lock probe
def tk.one(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>, old: {Staging.sp_all_old(now, own <> inner) == True{} : Bool}) -> {Sg.judge(c, l, now, own, inner) == Sg.judge.free(c, l) : Sg.Plan}:
  %LA.rr.judge_old(c, l, now, own, inner) : {_ == Sg.judge.free(c, l) : Sg.Plan}
  %Equal.sym(Bool, Staging.sp_all_old(now, own <> inner), True{}, old) : {Sg.judge.go(_, c, l) == Sg.judge.free(c, l) : Sg.Plan}
  {==}

def Staging.sweep_takes_stale_free_real(now, own, inner, old):
  +h = old
  (tk.one(Sg.CDir{}, Sg.LFree{}, now, own, inner, h), (tk.one(Sg.CDir{}, Sg.LAbsent{}, now, own, inner, h), tk.one(Sg.CLock{}, Sg.LFree{}, now, own, inner, h)))
