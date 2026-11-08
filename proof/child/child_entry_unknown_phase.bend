# eukhe: the proof of LAW child_entry_unknown_phase
#
# PROOF: a phase tag past 2 reads back and is unknown, so the phase is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def up.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_ph.tag(FCh.tag.of(3n+n), rest) : Wr.Dec<Ch.Ph>}:
  match n:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          {==}

def Child.child_entry_unknown_phase(n, rest, fit):
  +R = Wr.err("child: bad phase")
  %LWire.pw6.nat(2n, Wr.put_nat(3n+n, rest), {==}) : {FCh.run(_) == R : String}
  %LWire.pw6.nat(3n+n, rest, fit) : {FCh.abort.ph(FCh.get_ph.go(_)) == R : String}
  %up.tag(n, rest) : {FCh.abort.ph(_) == R : String}
  {==}
