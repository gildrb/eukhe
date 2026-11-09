# eukhe: the proof of LAW child_entry_bad_mode
#
# PROOF: the request tag, settings, clock, elapsed ms and poll read
# back; the mode tag does not read, so the verdict answers the mode error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_bad_mode(c, w, e, o, rest, hc, hw, he, ho, bad):
  +R = Wr.err("child: bad mode")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, rest)))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, rest))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Child.ch_spell_obs(o, rest)), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Child.ch_spell_obs(o, rest), he) : {FCh.verdict.e(c, w, _) == R : String}
  %LA.rt.obs(o, rest, ho) : {FCh.verdict.o(c, w, e, _) == R : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {FCh.verdict.m(c, w, e, o, FCh.get_mode.go(_)) == R : String}
  {==}
