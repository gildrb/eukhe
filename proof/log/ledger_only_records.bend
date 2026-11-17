# eukhe: the proof of LAW ledger_only_records
#
# By induction on the operations (ledger_base.bend, lb.only_hist): what a
# history leaves starts with the log of the file before it, or with the
# durable part of that log when a later crash lost a file whose entries
# were not durable (its operations then keep none of their records); then
# a prefix of each operation's records. From a file with durable entries
# both starts are its log.

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./ledger_base.bend as LB

def pl.only_top(-d: Lg.Disk, -es: List<&2, Lg.Epoch>, c: &w: Bool -> &ns: List<&2, Nat> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(es, Log.log_ledger_start(d)))) == List.append(&2, List<&2, Nat>, LB.lb.pick(w, Log.log_ledger_start(d)), Log.log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}) -> &ns: List<&2, Nat> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}:
  match c:
    case (+w, c2):
      match c2:
        case (+ns, h):
          (ns, LB.lb.pk(w, d, Lg.Disk.log(Log.log_ledger_after(es, d)), Log.log_ledger_taken(es, ns), h))

def pl.only(+d: Lg.Disk, es: List<&2, Lg.Epoch>) -> &ns: List<&2, Nat> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}:
  pl.only_top(d, es, LB.lb.only_hist(es, Log.log_ledger_start(d), LB.lb.ok0(d)))

def Log.ledger_only_records(d, es):
  pl.only(d, es)
