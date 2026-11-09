# eukhe: the proof of LAW child_entry_bad_delete_flag
#
# PROOF: the request tag 2 and the phase read back; the flag does not
# read, so the abort answers the delete flag error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_delete_flag(p, rest, hp, bad):
  +R = Wr.err("child: bad delete flag")
  %LWire.pw6.nat(2n, Child.ch_spell_ph(p, rest), {==}) : {FCh.run(_) == R : String}
  %LA.rt.ph(p, rest, hp) : {FCh.abort.ph(_) == R : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(rest), Wr.Bad{}, bad) : {FCh.abort.d(p, _) == R : String}
  {==}
