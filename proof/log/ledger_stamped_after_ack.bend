# eukhe: the proof of LAW ledger_stamped_after_ack
#
# The file a history leaves has durable entries when its stamp names it
# (lb.ok_hist); an operation's run that acknowledged a record linked the
# stamp before it, with both entries durable, which every crash keeps
# (lb.view, lb.saj).

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./ledger_base.bend as LB

def pl.sa(+d: Lg.Disk, +es: List<&2, Lg.Epoch>, +e: Lg.Epoch, h: {List.is_empty(&2, List<&2, Nat>, Log.log_ledger_acked(Log.log_ledger_rest(es, Log.log_ledger_start(d)), e)) == False{} : Bool}) -> {Lg.Rest.kept(Log.log_ledger_step(Log.log_ledger_rest(es, Log.log_ledger_start(d)), e)) == True{} : Bool}:
  +r = Log.log_ledger_rest(es, Log.log_ledger_start(d))
  LB.lb.sa_v(r, e, LB.lb.view(r, e, LB.lb.ok_hist(es, Log.log_ledger_start(d), LB.lb.ok0(d))), h)

def Log.ledger_stamped_after_ack(d, es, e, acked):
  pl.sa(d, es, e, acked)
