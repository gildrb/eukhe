# eukhe: the proof of LAW child_entry_unknown_report
#
# PROOF: the owing tag reads back; a report tag past 4 reads back and is
# TBad, so the phase is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def Child.child_entry_unknown_report(n, rest, fit):
  +R = Wr.err("child: bad phase")
  %LWire.pw6.nat(2n, Wr.put_nat(1n, Wr.put_nat(5n+n, rest)), {==}) : {FCh.run(_) == R : String}
  %LWire.pw6.nat(1n, Wr.put_nat(5n+n, rest), {==}) : {FCh.abort.ph(FCh.get_ph.go(_)) == R : String}
  %LWire.pw6.nat(5n+n, rest, fit) : {FCh.abort.ph(FCh.get_ph.owing(FCh.get_report.go(_))) == R : String}
  {==}
