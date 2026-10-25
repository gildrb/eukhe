# eukhe: the proof of LAW repeat_system_ignored

import Base
import ../../bend/repeat.bend as Rp
import ../../bend/ffi_repeat.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/repeat.bend as Repeat
import ./base.bend as LARepeat

# PROOF of LAW repeat_system_ignored: by induction on the newer messages: a system message gives the drive back its walk unchanged.

def rp.sys.go(xs: List<&2, Rp.Ev>, +n: Rp.Next, +ys: List<&2, Rp.Ev>) -> {Repeat.drive(List.append(&2, Rp.Ev, xs, Rp.System{} <> ys), n) == Repeat.drive(List.append(&2, Rp.Ev, xs, ys), n) : Nat}:
  match xs:
    case Nil{}:
      match n:
        case Rp.Goes{w}:
          match w:
            case Rp.Walk{want, k, first, pend}:
              {==}
        case Rp.Stops{+c}:
          Equal.sym(Nat, Repeat.drive(ys, Rp.Stops{c}), c, LARepeat.rp.halted(ys, c))
    case +x <> t:
      match n:
        case Rp.Goes{+w}:
          rp.sys.go(t, Rp.step(w, x), ys)
        case Rp.Stops{c}:
          {==}

def Repeat.repeat_system_ignored(xs, w, ys):
  rp.sys.go(xs, Rp.Goes{w}, ys)
