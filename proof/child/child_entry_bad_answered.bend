# eukhe: the proof of LAW child_entry_bad_answered
#
# PROOF: the request tag, settings, clock, elapsed ms and poll tag 2
# read back; the flag does not read, so the poll is Bad and the verdict
# answers the poll error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_answered(c, w, e, rest, hc, hw, he, bad):
  +R = Wr.err("child: bad poll")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(2n, rest)))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(2n, rest))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Wr.put_nat(2n, rest)), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Wr.put_nat(2n, rest), he) : {FCh.verdict.e(c, w, _) == R : String}
  %LWire.pw6.nat(2n, rest, {==}) : {FCh.verdict.o(c, w, e, FCh.get_obs.go(_)) == R : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(rest), Wr.Bad{}, bad) : {FCh.verdict.o(c, w, e, FCh.get_obs.answered(_)) == R : String}
  {==}
