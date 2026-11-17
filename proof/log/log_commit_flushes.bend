# eukhe: the proof of LAW log_commit_flushes
#
# The sidecars' appends flush nothing (lc.cnt_apps), their flushes one
# each (lc.cnt_fls); what follows computes, by the directory flush,
# main.jsonl's entry and the stamp (lc.cnt_tail), and the code's fresh test
# is the spec's (lc.fresh).

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./log_commit_base.bend as LC

def pf.count(fsync: Bool, +main: Bool, +stamp: Bool, +ds: List<&2, Bool>) -> {Log.log_flush_count(Log.log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds))) == Log.log_flush_due(fsync, main, ds) : Nat}:
  match fsync:
    case False{}:
      +tl = {[Lr.AppendMain{}, Lr.Ack{}] : List<&2, Lr.Act>}
      %Equal.sym(Nat, Log.log_flush_count(Lr.plan.appends(ds, 0n, tl)), Log.log_flush_count(tl), LC.lc.cnt_apps(ds, 0n, tl)) : {_ == 0n : Nat}
      {==}
    case True{}:
      +d = Lr.plan.dir(Lr.plan.fresh(ds), LC.lc.aft(main, stamp))
      +fl = Lr.plan.flushes(ds, 0n, d)
      +want = Nat.add(List.length(&2, Bool, ds), Nat.add(Log.log_bit(Log.log_fresh(ds)), 1n+Log.log_bit(Bool.not(main))))
      %Equal.sym(Nat, Log.log_flush_count(Lr.plan.appends(ds, 0n, fl)), Log.log_flush_count(fl), LC.lc.cnt_apps(ds, 0n, fl)) : {_ == want : Nat}
      %Equal.sym(Nat, Log.log_flush_count(fl), Nat.add(List.length(&2, Bool, ds), Log.log_flush_count(d)), LC.lc.cnt_fls(ds, 0n, d)) : {_ == want : Nat}
      %LC.lc.fresh(ds) : {Nat.add(List.length(&2, Bool, ds), Log.log_flush_count(d)) == Nat.add(List.length(&2, Bool, ds), Nat.add(Log.log_bit(_), 1n+Log.log_bit(Bool.not(main)))) : Nat}
      %LC.lc.cnt_tail(Lr.plan.fresh(ds), main, stamp) : {Nat.add(List.length(&2, Bool, ds), Log.log_flush_count(d)) == Nat.add(List.length(&2, Bool, ds), _) : Nat}
      {==}

def Log.log_commit_flushes(fsync, main, stamp, ds):
  pf.count(fsync, main, stamp, ds)
