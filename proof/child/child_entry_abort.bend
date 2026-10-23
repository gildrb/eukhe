# eukhe: the proof of LAW child_entry_abort

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../base/wire.bend as LWire
import ./base.bend as LA

def pw6.report(k: Ch.Report, +rest: String) -> {Wr.Got{k, rest} == FCh.get_report(FCh.put_report(k, rest)) : Wr.Dec<Ch.Report>}:
  match k:
    case Ch.Completed{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Completed{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Failed{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Failed{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Cancelled{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Cancelled{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Stalled{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Stalled{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Unreachable{}:
      %LWire.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Unreachable{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}

def pw6.ph(p: Ch.Ph, +rest: String, +h: {Child.wire_ph_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FCh.get_ph(FCh.put_ph(p, rest)) : Wr.Dec<Ch.Ph>}:
  match p:
    case Ch.Watching{+w}:
      %LWire.pw6.nat(0n, FCh.put_w(w, rest), {==}) : {Wr.Got{Ch.Watching{w}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %LA.pw6.w(w, rest, h) : {Wr.Got{Ch.Watching{w}, rest} == FCh.get_ph.watching(_) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Owing{+k, +n}:
      %LWire.pw6.nat(1n, FCh.put_report(k, Wr.put_nat(n, rest)), {==}) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %pw6.report(k, Wr.put_nat(n, rest)) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.owing(_) : Wr.Dec<Ch.Ph>}
      %LWire.pw6.nat(n, rest, h) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.n(k, _) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Ended{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Ended{}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      {==}

def Child.child_entry_abort(p, d, hp):
  +R = FCh.put_ph(Ch.cut.ph(p, d), "")
  %LWire.pw6.nat(2n, FCh.put_ph(p, Wr.put_bool(d, "")), {==}) : {FCh.run(_) == R : String}
  %pw6.ph(p, Wr.put_bool(d, ""), hp) : {FCh.abort.ph(_) == R : String}
  %LA.pw6.bool(d, "") : {FCh.abort.d(p, _) == R : String}
  {==}
