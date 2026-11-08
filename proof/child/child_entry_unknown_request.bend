# eukhe: the proof of LAW child_entry_unknown_request
#
# PROOF: the tag reads back (it fits); tags 3, 4 and every tag past 4 are
# unknown requests.

import Base
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../base/wire.bend as LWire

def uk.tag(n: Nat, rest: String) -> {FCh.run.tag(FCh.tag.of(3n+n), rest) == Wr.err("child: unknown request") : String}:
  match n:
    case 0n:
      {==}
    case 1n+d:
      match d:
        case 0n:
          {==}
        case 1n+e:
          {==}

def Child.child_entry_unknown_request(n, rest, fit):
  %LWire.pw6.nat(3n+n, rest, fit) : {FCh.run(_) == Wr.err("child: unknown request") : String}
  uk.tag(n, rest)
