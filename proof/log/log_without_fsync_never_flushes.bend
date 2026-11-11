# eukhe: the proof of LAW log_without_fsync_never_flushes
#
# The open without fsync has no step and leaves fsync off. A commit of a
# storage with fsync off is its appends, the marker and the ack (no flush:
# pnf.appends) and leaves fsync off, so the next commit is the same
# (pnf.session).

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

# the appends of the sidecars from the i-th, then the marker and the ack,
# hold no flush
def pnf.appends(ds: List<&2, Bool>, +i: Nat) -> {Log.log_any_flush(Lr.plan.appends(ds, i, [Lr.AppendMain{}, Lr.Ack{}])) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      pnf.appends(more, 1n+i)

# no commit of a storage with fsync off flushes, whatever main.jsonl's entry
def pnf.session(dss: List<&2, List<&2, Bool>>, +main: Bool) -> {Log.log_session_flushes(dss, Lr.Store{False{}, main}) == False{} : Bool}:
  match dss:
    case Nil{}:
      {==}
    case +ds <> rest:
      %Equal.sym(Bool, Log.log_any_flush(Lr.plan.appends(ds, 0n, [Lr.AppendMain{}, Lr.Ack{}])), False{}, pnf.appends(ds, 0n)) : {Bool.or(_, Log.log_session_flushes(rest, Lr.Store{False{}, main})) == False{} : Bool}
      pnf.session(rest, main)

def Log.log_without_fsync_never_flushes(dss):
  pnf.session(dss, False{})
