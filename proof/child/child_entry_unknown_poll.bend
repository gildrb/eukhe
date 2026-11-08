# eukhe: the proof of LAW child_entry_unknown_poll
#
# PROOF: the settings, clock and elapsed ms read back; a poll tag past 4
# reads back and is TBad, so the poll is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_unknown_poll(c, w, e, n, rest, hc, hw, he, fit):
  +R = Wr.err("child: bad poll")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(5n+n, rest)))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(5n+n, rest))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Wr.put_nat(5n+n, rest)), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Wr.put_nat(5n+n, rest), he) : {FCh.verdict.e(c, w, _) == R : String}
  %LWire.pw6.nat(5n+n, rest, fit) : {FCh.verdict.o(c, w, e, FCh.get_obs.go(_)) == R : String}
  {==}
