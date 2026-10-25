# eukhe: the proof of LAW repeat_said_ends

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

# PROOF of LAW repeat_said_ends: by induction on the newer messages: once the drive reaches the reply with no call, it stops with the count it answers at the context's end (rp.halted).

def rp.repeat_said_ends.go(xs: List<&2, Rp.Ev>, +n: Rp.Next, +ys: List<&2, Rp.Ev>) -> {Repeat.drive(List.append(&2, Rp.Ev, xs, Rp.Said{} <> ys), n) == Repeat.drive(xs, n) : Nat}:
  match xs:
    case Nil{}:
      match n:
        case Rp.Goes{w}:
          match w:
            case Rp.Walk{want, +k, first, pend}:
              LARepeat.rp.halted(ys, Rp.count(k))
        case Rp.Stops{c}:
          {==}
    case +x <> t:
      match n:
        case Rp.Goes{+w}:
          rp.repeat_said_ends.go(t, Rp.step(w, x), ys)
        case Rp.Stops{c}:
          {==}

def Repeat.repeat_said_ends(xs, w, ys):
  rp.repeat_said_ends.go(xs, Rp.Goes{w}, ys)
