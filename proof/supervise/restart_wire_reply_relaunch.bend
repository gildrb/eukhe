# eukhe: the proof of LAW restart_wire_reply_relaunch

import Base
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../bend/ffi_supervise.bend as FS
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def Laws.restart_wire_reply_relaunch(ages, hs, f, hf, p, hp, rest):
  +r = rest
  %LA.ps.ffi_list(ages, FS.put_verdict(Su.Relaunch{f, p}, r), hs) : {FS.get_reply.ages(_) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, r} : Wr.Dec<FS.Reply>}
  %L.ps.ffi_nat(f, Wr.put_nat(p, r), hf) : {FS.get_reply.verdict(ages, FS.get_verdict.relaunch(_)) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, r} : Wr.Dec<FS.Reply>}
  %L.ps.ffi_nat(p, r, hp) : {FS.get_reply.verdict(ages, FS.get_verdict.backoff(f, _)) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, r} : Wr.Dec<FS.Reply>}
  {==}
