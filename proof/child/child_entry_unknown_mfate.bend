# eukhe: the proof of LAW child_entry_unknown_mfate
#
# PROOF: the presence tag reads back and is unknown, so the fate is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def umf.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_mfate.tag(FCh.tag.of(2n+n), rest) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match n:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              {==}

def Child.child_entry_unknown_mfate(n, rest, fit):
  +R = Wr.err("child: bad fate")
  %LWire.pw6.nat(1n, Wr.put_nat(2n+n, rest), {==}) : {FCh.run(_) == R : String}
  %LWire.pw6.nat(2n+n, rest, fit) : {FCh.move.f(FCh.get_mfate.go(_)) == R : String}
  %umf.tag(n, rest) : {FCh.move.f(_) == R : String}
  {==}
