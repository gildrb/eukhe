# eukhe: the proof of LAW once_entry_reads
#
# PROOF: the entry reads every input as the laws' reader does
# (LE.oe.read); every cap that reader answers fits the wire
# (LE.oe.fit_go), so a whole event runs as the same event spelled
# (LE.oe.spelled).

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ./base.bend as LA
import ./base/entry.bend as LE

def oer.got(+l: O.Life, d: Wr.Dec<FO.Ev>, +e: FO.Ev, fd: LE.oe.FitD(d), got: {Once.on_read.whole(d) == Some{e} : Maybe<&2, FO.Ev>}) -> {FO.step.got(d, l) == FO.step(FO.Eff{l}, Once.on_spell(e)) : FO.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LA.ob.some_inj(FO.Ev, x, e, got) : {FO.step.ev(x, l) == FO.step(FO.Eff{l}, Once.on_spell(_)) : FO.St & String}
          Equal.sym(FO.St & String, FO.step(FO.Eff{l}, Once.on_spell(x)), FO.step.ev(x, l), LE.oe.spelled(l, x, fd))
        case SCon{h, t}:
          LA.ob.none_some(FO.Ev, {FO.step.end(False{}, x, l) == FO.step(FO.Eff{l}, Once.on_spell(e)) : FO.St & String}, e, got)
    case Wr.Bad{}:
      LA.ob.none_some(FO.Ev, {(FO.Eff{l}, FO.fail()) == FO.step(FO.Eff{l}, Once.on_spell(e)) : FO.St & String}, e, got)

def Once.once_entry_reads(l, i, e, got):
  %LE.oe.read(Wr.get_nat(i)) : {FO.step.got(_, l) == FO.step(FO.Eff{l}, Once.on_spell(e)) : FO.St & String}
  oer.got(l, Once.on_read.go(Wr.get_nat(i)), e, LE.oe.fit_go(Wr.get_nat(i)), got)
