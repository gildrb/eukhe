# eukhe: the proof of LAW child_entry_unknown_busy_token
#
# PROOF: the request tag, settings, clock, elapsed ms and poll tag 0
# read back; the token tag reads back and is unknown (ub.tag), so the
# poll is Bad and the verdict answers the poll error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def ub.tag(n: Nat, rest: String) -> {Wr.Bad{} == FCh.get_maybe_nat.tag(FCh.tag.of(2n+n), rest) : Wr.Dec<Maybe<&2, Nat>>}:
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

def Child.child_entry_unknown_busy_token(c, w, e, n, rest, hc, hw, he, fit):
  +R = Wr.err("child: bad poll")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(0n, Wr.put_nat(2n+n, rest))))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(0n, Wr.put_nat(2n+n, rest)))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Wr.put_nat(0n, Wr.put_nat(2n+n, rest))), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Wr.put_nat(0n, Wr.put_nat(2n+n, rest)), he) : {FCh.verdict.e(c, w, _) == R : String}
  %LWire.pw6.nat(0n, Wr.put_nat(2n+n, rest), {==}) : {FCh.verdict.o(c, w, e, FCh.get_obs.go(_)) == R : String}
  %LWire.pw6.nat(2n+n, rest, fit) : {FCh.verdict.o(c, w, e, FCh.get_obs.busy(FCh.get_maybe_nat.go(_))) == R : String}
  %ub.tag(n, rest) : {FCh.verdict.o(c, w, e, FCh.get_obs.busy(_)) == R : String}
  {==}
