# eukhe: the proof of LAW child_entry_bad_clock
#
# PROOF: the request tag and the settings read back; the cut clock
# decodes to Bad (LA.ct.clock), so the verdict answers the clock error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_clock(c, k, rest, hc, fit, bad):
  +R = Wr.err("child: bad clock")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_cut_clock(k, rest)), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_cut_clock(k, rest), hc) : {FCh.verdict.c(_) == R : String}
  %LA.ct.clock(k, rest, fit, bad) : {FCh.verdict.w(c, _) == R : String}
  {==}
