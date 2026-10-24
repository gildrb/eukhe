# eukhe: the proof of LAW log_commit_plan
#
# Each piece of the plan is the spec's piece: the appends and the flushes
# of the sidecars from any index (pl.apps, pl.flushes), the directory flush
# when an entry is fresh (pl.dir, pl.fresh); the spec's appends of lists
# then compute away, case by case on fsync and main.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def pl.apps(ds: List<&2, Bool>, +i: Nat, +rest: List<&2, Lr.Act>) -> {Lr.plan.appends(ds, i, rest) == List.append(&2, Lr.Act, Log.log_appends(Log.log_ixs(ds, i)), rest) : List<&2, Lr.Act>}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      %pl.apps(more, 1n+i, rest) : {Lr.AppendSide{i} <> Lr.plan.appends(more, 1n+i, rest) == Lr.AppendSide{i} <> _ : List<&2, Lr.Act>}
      {==}

def pl.flushes(ds: List<&2, Bool>, +i: Nat, +rest: List<&2, Lr.Act>) -> {Lr.plan.flushes(ds, i, rest) == List.append(&2, Lr.Act, Log.log_flushes(Log.log_ixs(ds, i)), rest) : List<&2, Lr.Act>}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      %pl.flushes(more, 1n+i, rest) : {Lr.FlushSide{i} <> Lr.plan.flushes(more, 1n+i, rest) == Lr.FlushSide{i} <> _ : List<&2, Lr.Act>}
      {==}

def pl.dir(b: Bool, rest: List<&2, Lr.Act>) -> {Lr.plan.dir(b, rest) == List.append(&2, Lr.Act, Log.log_dir(b), rest) : List<&2, Lr.Act>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pl.fresh(ds: List<&2, Bool>) -> {Lr.plan.fresh(ds) == Log.log_fresh(ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      match d:
        case True{}:
          pl.fresh(more)
        case False{}:
          {==}

# with fsync, for main.jsonl's entry durable (tail [Ack]) or not
# (tail [FlushDir, Ack])
def pl.synced(+ds: List<&2, Bool>, +tail: List<&2, Lr.Act>) -> {Lr.plan.appends(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), Lr.AppendMain{} <> Lr.FlushMain{} <> tail))) == List.append(&2, Lr.Act, Log.log_appends(Log.log_ixs(ds, 0n)), List.append(&2, Lr.Act, Log.log_flushes(Log.log_ixs(ds, 0n)), List.append(&2, Lr.Act, Log.log_dir(Log.log_fresh(ds)), Lr.AppendMain{} <> Lr.FlushMain{} <> tail))) : List<&2, Lr.Act>}:
  +mid = {Lr.AppendMain{} <> Lr.FlushMain{} <> tail : List<&2, Lr.Act>}
  +fl = Log.log_flushes(Log.log_ixs(ds, 0n))
  +ap = Log.log_appends(Log.log_ixs(ds, 0n))
  %pl.fresh(ds) : {Lr.plan.appends(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid))) == List.append(&2, Lr.Act, ap, List.append(&2, Lr.Act, fl, List.append(&2, Lr.Act, Log.log_dir(_), mid))) : List<&2, Lr.Act>}
  %pl.dir(Lr.plan.fresh(ds), mid) : {Lr.plan.appends(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid))) == List.append(&2, Lr.Act, ap, List.append(&2, Lr.Act, fl, _)) : List<&2, Lr.Act>}
  %pl.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid)) : {Lr.plan.appends(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid))) == List.append(&2, Lr.Act, ap, _) : List<&2, Lr.Act>}
  %pl.apps(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid))) : {Lr.plan.appends(ds, 0n, Lr.plan.flushes(ds, 0n, Lr.plan.dir(Lr.plan.fresh(ds), mid))) == _ : List<&2, Lr.Act>}
  {==}

def Log.log_commit_plan(fsync, main, ds):
  match fsync:
    case False{}:
      %pl.apps(ds, 0n, [Lr.AppendMain{}, Lr.Ack{}]) : {Lr.Store.commit(Lr.Store{False{}, main}, ds) == Lr.Plan{Lr.Store{False{}, main}, _} : Lr.Plan}
      {==}
    case True{}:
      match main:
        case True{}:
          %pl.synced(ds, [Lr.Ack{}]) : {Lr.Store.commit(Lr.Store{True{}, True{}}, ds) == Lr.Plan{Lr.Store{True{}, True{}}, _} : Lr.Plan}
          {==}
        case False{}:
          %pl.synced(ds, [Lr.FlushDir{}, Lr.Ack{}]) : {Lr.Store.commit(Lr.Store{True{}, False{}}, ds) == Lr.Plan{Lr.Store{True{}, True{}}, _} : Lr.Plan}
          {==}
