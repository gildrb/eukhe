# eukhe: the proof of LAW child_entry_bad_id
#
# PROOF: the request tag and the spelled fate presence read back, so the
# move's id stage reads the rest, which does not read as a Nat.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_id(f, rest, bad):
  +R = Wr.err("child: bad id")
  %LWire.pw6.nat(1n, Child.ch_spell_mfate(f, rest), {==}) : {FCh.run(_) == R : String}
  %LA.rt.mfate(f, rest) : {FCh.move.f(_) == R : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {FCh.move.n(f, _) == R : String}
  {==}
