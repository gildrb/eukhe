# eukhe: the proof of LAW ledger_ack_durable
#
# By induction on the operations (ledger_base.bend, lb.ack_hist): what a
# history leaves starts with the log of the file before it, or with the
# durable part of that log when a later crash lost a file whose entries
# were not durable; then each operation's acknowledged records, each
# followed by maybe more. An operation runs one of three runs of the model
# (lb.view); a file its stamp names has durable entries all along
# (lb.ok_hist). From a file with durable entries both starts are its log.

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./ledger_base.bend as LB

def pl.ack_top(-d: Lg.Disk, -es: List<&2, Lg.Epoch>, c: &w: Bool -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(es, Log.log_ledger_start(d)))) == List.append(&2, List<&2, Nat>, LB.lb.pick(w, Log.log_ledger_start(d)), Log.log_ledger_kept.r(es, Log.log_ledger_start(d), xs)) : List<&2, List<&2, Nat>>}) -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_kept(es, d, xs)) : List<&2, List<&2, Nat>>}:
  match c:
    case (+w, c2):
      match c2:
        case (+xs, h):
          (xs, LB.lb.pk(w, d, Lg.Disk.log(Log.log_ledger_after(es, d)), Log.log_ledger_kept(es, d, xs), h))

def pl.ack(+d: Lg.Disk, es: List<&2, Lg.Epoch>) -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_kept(es, d, xs)) : List<&2, List<&2, Nat>>}:
  pl.ack_top(d, es, LB.lb.ack_hist(es, Log.log_ledger_start(d), LB.lb.ok0(d)))

def Log.ledger_ack_durable(d, es):
  pl.ack(d, es)
