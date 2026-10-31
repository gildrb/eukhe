# eukhe: the proof of LAW snapshot_best_is_best: the snapshot's best is
# the segment's last kept metric, which best_is_best pins

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./best_is_best.bend as PBestIsBest

def SnapshotBestIsBest.of(s: ArS.St, h: AutoresearchHistory.ar_best_ok(s)) -> AutoresearchHistory.ar_snap_best_ok(s):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match cfg:
        case None{}:
          h
        case Some{c}:
          h

def AutoresearchHistory.snapshot_best_is_best(evs):
  SnapshotBestIsBest.of(ArM.ar_run(evs), AutoresearchHistory.best_is_best(evs))
