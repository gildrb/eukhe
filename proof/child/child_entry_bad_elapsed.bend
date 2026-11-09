# eukhe: the proof of LAW child_entry_bad_elapsed
#
# PROOF: the request tag, settings and clock read back; the elapsed ms
# do not read, so the verdict answers the elapsed ms error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_elapsed(c, w, rest, hc, hw, bad):
  +R = Wr.err("child: bad elapsed ms")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, rest)), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, rest), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, rest, hw) : {FCh.verdict.w(c, _) == R : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {FCh.verdict.e(c, w, _) == R : String}
  {==}
