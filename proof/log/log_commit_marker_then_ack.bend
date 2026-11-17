# eukhe: the proof of LAW log_commit_marker_then_ack
#
# The walk of main.jsonl passes over the sidecars' appends and flushes
# (lc.mw_apps, lc.mw_fls); what follows them computes, by the directory
# flush, main.jsonl's entry and the stamp (pm.unsynced, lc.mw_tail).

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./log_commit_base.bend as LC

# without fsync: the marker, then the ack
def pm.unsynced(main: Bool, stamp: Bool) -> {Log.log_main_walk([Lr.AppendMain{}, Lr.Ack{}], False{}, False{}, main, False{}, False{}, stamp, main) == True{} : Bool}:
  match main stamp:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pm.walk(fsync: Bool, +main: Bool, +stamp: Bool, +ds: List<&2, Bool>) -> {Log.log_main_walk(Log.log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), False{}, False{}, main, False{}, fsync, stamp, main) == True{} : Bool}:
  match fsync:
    case False{}:
      +tl = {[Lr.AppendMain{}, Lr.Ack{}] : List<&2, Lr.Act>}
      %Equal.sym(Bool, Log.log_main_walk(Lr.plan.appends(ds, 0n, tl), False{}, False{}, main, False{}, False{}, stamp, main), Log.log_main_walk(tl, False{}, False{}, main, False{}, False{}, stamp, main), LC.lc.mw_apps(ds, 0n, tl, False{}, False{}, main, False{}, False{}, stamp, main)) : {_ == True{} : Bool}
      pm.unsynced(main, stamp)
    case True{}:
      +d = Lr.plan.dir(Lr.plan.fresh(ds), LC.lc.aft(main, stamp))
      +fl = Lr.plan.flushes(ds, 0n, d)
      %Equal.sym(Bool, Log.log_main_walk(Lr.plan.appends(ds, 0n, fl), False{}, False{}, main, False{}, True{}, stamp, main), Log.log_main_walk(fl, False{}, False{}, main, False{}, True{}, stamp, main), LC.lc.mw_apps(ds, 0n, fl, False{}, False{}, main, False{}, True{}, stamp, main)) : {_ == True{} : Bool}
      %Equal.sym(Bool, Log.log_main_walk(fl, False{}, False{}, main, False{}, True{}, stamp, main), Log.log_main_walk(d, False{}, False{}, main, False{}, True{}, stamp, main), LC.lc.mw_fls(ds, 0n, d, False{}, False{}, main, False{}, True{}, stamp, main)) : {_ == True{} : Bool}
      LC.lc.mw_tail(Lr.plan.fresh(ds), main, stamp)

def Log.log_commit_marker_then_ack(fsync, main, stamp, ds):
  pm.walk(fsync, main, stamp, ds)
