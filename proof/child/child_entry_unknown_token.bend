# eukhe: the proof of LAW child_entry_unknown_token
#
# PROOF: the settings read back; the token tag reads back and is unknown,
# so the clock is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def ut.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_maybe_nat.tag(FCh.tag.of(2n+n), rest) : Wr.Dec<Maybe<&2, Nat>>}:
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

def Child.child_entry_unknown_token(c, n, rest, hc, fit):
  +R = Wr.err("child: bad clock")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Wr.put_nat(2n+n, rest)), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Wr.put_nat(2n+n, rest), hc) : {FCh.verdict.c(_) == R : String}
  %LWire.pw6.nat(2n+n, rest, fit) : {FCh.verdict.w(c, FCh.get_w.t(FCh.get_maybe_nat.go(_))) == R : String}
  %ut.tag(n, rest) : {FCh.verdict.w(c, FCh.get_w.t(_)) == R : String}
  {==}
