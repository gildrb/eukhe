# eukhe: the proof of LAW child_entry_bad_poll
#
# PROOF: the request tag, settings, clock and elapsed ms read back; the
# cut poll decodes to Bad (bp.cut: the tags spelled before the cut read
# back, then a number that does not read), so the verdict answers the poll
# error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def bp.cut(k: Child.ChPollCut, +rest: String, bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}) -> {Wr.Bad{} == FCh.get_obs(Child.ch_cut_poll(k, rest)) : Wr.Dec<Ch.Obs>}:
  match k:
    case Child.PollAtTag{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Child.PollAtBusyTag{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Bad{} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_obs.busy(FCh.get_maybe_nat.go(_)) : Wr.Dec<Ch.Obs>}
      {==}
    case Child.PollAtBusyToken{}:
      %LWire.pw6.nat(0n, Wr.put_nat(1n, rest), {==}) : {Wr.Bad{} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Bad{} == FCh.get_obs.busy(FCh.get_maybe_nat.go(_)) : Wr.Dec<Ch.Obs>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_obs.busy(FCh.get_maybe_nat.some(_)) : Wr.Dec<Ch.Obs>}
      {==}

def Child.child_entry_bad_poll(c, w, e, k, rest, hc, hw, he, bad):
  +R = Wr.err("child: bad poll")
  %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_cut_poll(k, rest)))), {==}) : {FCh.run(_) == R : String}
  %LA.rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_cut_poll(k, rest))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.rt.w(w, Wr.put_nat(e, Child.ch_cut_poll(k, rest)), hw) : {FCh.verdict.w(c, _) == R : String}
  %LWire.pw6.nat(e, Child.ch_cut_poll(k, rest), he) : {FCh.verdict.e(c, w, _) == R : String}
  %bp.cut(k, rest, bad) : {FCh.verdict.o(c, w, e, _) == R : String}
  {==}
