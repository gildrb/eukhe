# eukhe: the proof of LAW ledger_kept_flushes_once
#
# A kept open has no step and leaves main.jsonl's entry durable, so each
# commit is its append, its flush and its ack; by induction on the
# commits.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def pk.plan(cs: List<&2, List<&2, Nat>>) -> {Log.log_plan(cs, Lr.Store{True{}, True{}, True{}}) == Log.log_one_flush(cs) : List<&2, Log.LogDo>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      %pk.plan(rest) : {Log.LogDo{Lr.AppendMain{}, c} <> Log.LogDo{Lr.FlushMain{}, c} <> Log.LogDo{Lr.Ack{}, c} <> Log.log_plan(rest, Lr.Store{True{}, True{}, True{}}) == Log.LogDo{Lr.AppendMain{}, c} <> Log.LogDo{Lr.FlushMain{}, c} <> Log.LogDo{Lr.Ack{}, c} <> _ : List<&2, Log.LogDo>}
      {==}

def Log.ledger_kept_flushes_once(cs):
  pk.plan(cs)
