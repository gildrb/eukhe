# eukhe: the proof of LAW child_entry_unknown_watched_token
#
# PROOF: the request tag 2 and phase tag 0 read back; the clock's
# token tag reads back and is unknown (uw.tag), so the clock and the phase
# are Bad and the abort answers the phase error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def uw.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_maybe_nat.tag(FCh.tag.of(2n+n), rest) : Wr.Dec<Maybe<&2, Nat>>}:
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

def Child.child_entry_unknown_watched_token(n, rest, fit):
  +R = Wr.err("child: bad phase")
  %LWire.pw6.nat(2n, Wr.put_nat(0n, Wr.put_nat(2n+n, rest)), {==}) : {FCh.run(_) == R : String}
  %LWire.pw6.nat(0n, Wr.put_nat(2n+n, rest), {==}) : {FCh.abort.ph(FCh.get_ph.go(_)) == R : String}
  %LWire.pw6.nat(2n+n, rest, fit) : {FCh.abort.ph(FCh.get_ph.watching(FCh.get_w.t(FCh.get_maybe_nat.go(_)))) == R : String}
  %uw.tag(n, rest) : {FCh.abort.ph(FCh.get_ph.watching(FCh.get_w.t(_))) == R : String}
  {==}
