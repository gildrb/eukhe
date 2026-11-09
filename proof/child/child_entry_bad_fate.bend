# eukhe: the proof of LAW child_entry_bad_fate
#
# PROOF: the request tag 1 reads back; the cut fate decodes to Bad
# (bf.cut: presence 1 read back when spelled, then a number that does not
# read), so the move answers the fate error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def bf.cut(k: Child.ChFateCut, +rest: String, bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}) -> {Wr.Bad{} == FCh.get_mfate(Child.ch_cut_fate(k, rest)) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match k:
    case Child.FateAtPresence{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}
    case Child.FateAtTag{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Bad{} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_mfate.some(FCh.get_fate.go(_)) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}

def Child.child_entry_bad_fate(k, rest, bad):
  +R = Wr.err("child: bad fate")
  %LWire.pw6.nat(1n, Child.ch_cut_fate(k, rest), {==}) : {FCh.run(_) == R : String}
  %bf.cut(k, rest, bad) : {FCh.move.f(_) == R : String}
  {==}
