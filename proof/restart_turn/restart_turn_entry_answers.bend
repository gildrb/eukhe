# eukhe: the proof of LAW restart_turn_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (restart_turn_entry_reads), so the entry answers the model's answer,
# encoded as the spec spells it (rtm.reply).

import Base
import ../../bend/restart_turn.bend as Rt
import ../../bend/ffi_restart_turn.bend as FRt
import ../../bend/wire.bend as Wr
import ../../laws/restart_turn.bend as RestartTurn
import ./restart_turn_entry_reads.bend as PRestartTurnEntryReads

def rtm.reply(x: Rt.Next) -> {FRt.put_next(x) == RestartTurn.rt_w_reply(x) : String}:
  match x:
    case Rt.Continue{n}:
      {==}
    case Rt.End{n}:
      {==}
    case Rt.Relaunch{}:
      {==}
    case Rt.Retire{}:
      {==}

def RestartTurn.restart_turn_entry_answers(f, h):
  %Equal.sym(Wr.Dec<Rt.Fact>, FRt.get_req(RestartTurn.rt_w_req(f, "")), Wr.Got{f, ""}, RestartTurn.restart_turn_entry_reads(f, "", h)) : {FRt.ffi.got(_) == RestartTurn.rt_w_reply(Rt.next(f)) : String}
  rtm.reply(Rt.next(f))
