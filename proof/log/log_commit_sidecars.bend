# eukhe: the proof of LAW log_commit_sidecars
#
# Split on the commit's sidecar i (log_nth). None: no append or flush
# reaches i (lc.none_apps, lc.none_fls) and the rest touches no sidecar.
# Some{d}: the appends reach i once (lc.apps), the flushes flush it
# (lc.fl), and the directory flush makes its entry durable when d is not
# (lc.fresh_some, lc.dir_some); without fsync the marker follows the
# appends.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./log_commit_base.bend as LC

def ps.none(fsync: Bool, +main: Bool, +stamp: Bool, +ds: List<&2, Bool>, +i: Nat, +h: {LC.lc.in(0n, i, ds) == False{} : Bool}) -> {Log.log_side_none(Log.log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), i) == True{} : Bool}:
  match fsync:
    case False{}:
      +tl = {[Lr.AppendMain{}, Lr.Ack{}] : List<&2, Lr.Act>}
      %Equal.sym(Bool, Log.log_side_none(Lr.plan.appends(ds, 0n, tl), i), Log.log_side_none(tl, i), LC.lc.none_apps(ds, 0n, i, tl, h)) : {_ == True{} : Bool}
      {==}
    case True{}:
      +a = LC.lc.aft(main, stamp)
      +d = Lr.plan.dir(Lr.plan.fresh(ds), a)
      +fl = Lr.plan.flushes(ds, 0n, d)
      %Equal.sym(Bool, Log.log_side_none(Lr.plan.appends(ds, 0n, fl), i), Log.log_side_none(fl, i), LC.lc.none_apps(ds, 0n, i, fl, h)) : {_ == True{} : Bool}
      %Equal.sym(Bool, Log.log_side_none(fl, i), Log.log_side_none(d, i), LC.lc.none_fls(ds, 0n, i, d, h)) : {_ == True{} : Bool}
      %Equal.sym(Bool, Log.log_side_none(d, i), Log.log_side_none(a, i), LC.lc.none_dir(Lr.plan.fresh(ds), a, i)) : {_ == True{} : Bool}
      LC.lc.none_aft(main, stamp, i)

def ps.some(fsync: Bool, +main: Bool, +stamp: Bool, +ds: List<&2, Bool>, +i: Nat, +x: Bool, +h: {LC.lc.in(0n, i, ds) == True{} : Bool}, +hb: {Bool.or(x, Lr.plan.fresh(ds)) == True{} : Bool}) -> {Log.log_side_walk(Log.log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), i, False{}, False{}, x, fsync) == True{} : Bool}:
  match fsync:
    case False{}:
      +tl = {[Lr.AppendMain{}, Lr.Ack{}] : List<&2, Lr.Act>}
      +r = LC.lc.in(0n, i, ds)
      %Equal.sym(Bool, Log.log_side_walk(Lr.plan.appends(ds, 0n, tl), i, False{}, False{}, x, False{}), Log.log_side_walk(tl, i, r, Bool.and(Bool.not(r), False{}), x, False{}), LC.lc.apps(ds, 0n, i, tl, False{}, x, False{})) : {_ == True{} : Bool}
      %Equal.sym(Bool, r, True{}, h) : {Log.log_side_walk(tl, i, _, Bool.and(Bool.not(_), False{}), x, False{}) == True{} : Bool}
      {==}
    case True{}:
      +a = LC.lc.aft(main, stamp)
      +d = Lr.plan.dir(Lr.plan.fresh(ds), a)
      +fl = Lr.plan.flushes(ds, 0n, d)
      +r = LC.lc.in(0n, i, ds)
      %Equal.sym(Bool, Log.log_side_walk(Lr.plan.appends(ds, 0n, fl), i, False{}, False{}, x, True{}), Log.log_side_walk(fl, i, r, Bool.and(Bool.not(r), False{}), x, True{}), LC.lc.apps(ds, 0n, i, fl, False{}, x, True{})) : {_ == True{} : Bool}
      %Equal.sym(Bool, r, True{}, h) : {Log.log_side_walk(fl, i, _, Bool.and(Bool.not(_), False{}), x, True{}) == True{} : Bool}
      %Equal.sym(Bool, Log.log_side_walk(fl, i, True{}, False{}, x, True{}), Log.log_side_walk(d, i, True{}, Bool.or(r, False{}), x, True{}), LC.lc.fl(ds, 0n, i, d, False{}, x, True{})) : {_ == True{} : Bool}
      %Equal.sym(Bool, r, True{}, h) : {Log.log_side_walk(d, i, True{}, Bool.or(_, False{}), x, True{}) == True{} : Bool}
      LC.lc.dir_some(Lr.plan.fresh(ds), x, main, stamp, i, hb)

def ps.side(m: Maybe<&2, Bool>, fsync: Bool, main: Bool, stamp: Bool, +ds: List<&2, Bool>, +i: Nat, +h: {Log.log_nth(ds, i) == m : Maybe<&2, Bool>}) -> {Log.log_side(Log.log_acts(Lr.Store.commit(Lr.Store{fsync, main, stamp}, ds)), i, m, fsync) == True{} : Bool}:
  match m:
    case None{}:
      ps.none(fsync, main, stamp, ds, i, LC.lc.in_none(ds, i, h))
    case Some{+x}:
      ps.some(fsync, main, stamp, ds, i, x, LC.lc.in_some(ds, i, x, h), LC.lc.fresh_some(ds, i, x, h))

def Log.log_commit_sidecars(fsync, main, stamp, ds, i):
  ps.side(Log.log_nth(ds, i), fsync, main, stamp, ds, i, {==})
