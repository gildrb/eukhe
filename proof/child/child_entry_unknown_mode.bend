# eukhe: the proof of LAW child_entry_unknown_mode
#
# PROOF: the settings, clock, elapsed ms and poll read back; a mode tag
# past 1 reads back and is unknown, so the mode is Bad.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def um.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_mode.tag(FCh.tag.of(2n+n), rest) : Wr.Dec<Ch.Mode>}:
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

def Child.child_entry_unknown_mode(c, w, e, o, n, rest, hc, hw, he, ho, fit):
  +R = Wr.err("child: bad mode")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Wr.put_nat(2n+n, rest))))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Wr.put_nat(2n+n, rest)))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Wr.put_nat(2n+n, rest))), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Child.ch_spell_obs(o, Wr.put_nat(2n+n, rest)), he) : {FCh.verdict.e(c, w, _) == R : String}
  %LA.rt.obs(o, Wr.put_nat(2n+n, rest), ho) : {FCh.verdict.o(c, w, e, _) == R : String}
  %LWire.pw6.nat(2n+n, rest, fit) : {FCh.verdict.m(c, w, e, o, FCh.get_mode.go(_)) == R : String}
  %um.tag(n, rest) : {FCh.verdict.m(c, w, e, o, _) == R : String}
  {==}
