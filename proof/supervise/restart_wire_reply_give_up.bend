# eukhe: the proof of LAW restart_wire_reply_give_up

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ../base.bend as L
import ./base.bend as LA

def Supervise.restart_wire_reply_give_up(ages, hs, f, hf, rest):
  +r = rest
  %LA.ps.ffi_list(ages, FS.put_verdict(Su.GiveUp{f}, r), hs) : {FS.get_reply.ages(_) == Wr.Got{FS.Reply{ages, Su.GiveUp{f}}, r} : Wr.Dec<FS.Reply>}
  %L.ps.ffi_nat(f, r, hf) : {FS.get_reply.verdict(ages, FS.get_verdict.give_up(_)) == Wr.Got{FS.Reply{ages, Su.GiveUp{f}}, r} : Wr.Dec<FS.Reply>}
  {==}
