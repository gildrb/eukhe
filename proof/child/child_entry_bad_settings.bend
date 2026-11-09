# eukhe: the proof of LAW child_entry_bad_settings
#
# PROOF: the request tag 0 reads back; the cut settings decode to Bad
# (bs.cut: the stall read back when spelled, then a number that does not
# read), so the verdict's first stage answers the settings error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ./base.bend as LA

def bs.cut(k: Child.ChSetCut, +rest: String, fit: {Child.ch_cut_set_fits(k) == True{} : Bool}, bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}) -> {Wr.Bad{} == FCh.get_cfg(Child.ch_cut_set(k, rest)) : Wr.Dec<Ch.Cfg>}:
  match k:
    case Child.SetAtStall{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_cfg.s(_) : Wr.Dec<Ch.Cfg>}
      {==}
    case Child.SetAtFails{+s}:
      %LWire.pw6.nat(s, rest, fit) : {Wr.Bad{} == FCh.get_cfg.s(_) : Wr.Dec<Ch.Cfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(rest), Wr.Bad{}, bad) : {Wr.Bad{} == FCh.get_cfg.f(s, _) : Wr.Dec<Ch.Cfg>}
      {==}

def Child.child_entry_bad_settings(k, rest, fit, bad):
  +R = Wr.err("child: bad settings")
  %LWire.pw6.nat(0n, Child.ch_cut_set(k, rest), {==}) : {FCh.run(_) == R : String}
  %bs.cut(k, rest, fit, bad) : {FCh.verdict.c(_) == R : String}
  {==}
