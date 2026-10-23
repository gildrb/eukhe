# eukhe: the proof of LAW restart_ffi_decides

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise

def Supervise.restart_ffi_decides(s, c, ages, g, h):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(s), Wr.Got{FS.Req{c, ages, g}, ""}, h) : {FS.ffi.go(_) == FS.put_reply(FS.Reply{Su.St.ages(Su.Decision.st(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))), Su.Decision.verdict(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))}, "") : String}
  {==}
