# eukhe: the proof of LAW child_entry_bad_phase
#
# PROOF: the request tag 2 reads back; the cut phase decodes to Bad
# (bh.cut: the tags and fields spelled before the cut read back, a
# watched clock's cut through LA.ct.clock, then a number that does not
# read), so the abort answers the phase error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def bh.cut(k: Child.ChPhaseCut, +rest: String, +fit: {Child.ch_cut_phase_fits(k) == True{} : Bool}, bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}) -> {Wr.Bad{} == FCh.get_ph(Child.ch_cut_phase(k, rest)) : Wr.Dec<Ch.Ph>}:
  match k:
    case Child.PhAtTag{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      {==}
    case Child.PhAtClock{+c}:
      %LWire.pw6.nat(0n, Child.ch_cut_clock(c, rest), {==}) : {Wr.Bad{} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %LA.ct.clock(c, rest, fit, bad) : {Wr.Bad{} == FCh.get_ph.watching(_) : Wr.Dec<Ch.Ph>}
      {==}
    case Child.PhAtReport{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Bad{} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_ph.owing(FCh.get_report.go(_)) : Wr.Dec<Ch.Ph>}
      {==}
    case Child.PhAtOwedId{+r}:
      %LWire.pw6.nat(1n, Child.ch_spell_report(r, rest), {==}) : {Wr.Bad{} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %LA.rt.report(r, rest) : {Wr.Bad{} == FCh.get_ph.owing(_) : Wr.Dec<Ch.Ph>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_ph.n(r, _) : Wr.Dec<Ch.Ph>}
      {==}

def Child.child_entry_bad_phase(k, rest, fit, bad):
  +R = Wr.err("child: bad phase")
  %LWire.pw6.nat(2n, Child.ch_cut_phase(k, rest), {==}) : {FCh.run(_) == R : String}
  %bh.cut(k, rest, fit, bad) : {FCh.abort.ph(_) == R : String}
  {==}
