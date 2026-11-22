# eukhe: the proof of LAW work_left_entry_steer
#
# PROOF: the entry's decoder reads the four Bools back (Wire
# wire_bool_round_trip), then the progress tag 2 (Wire.wire_nat_round_trip:
# 2 fits the wire); get_stall refuses that tag, so the entry answers the
# error form.

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/wire.bend as Wire
import ../../laws/work_left.bend as WorkLeft
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def WorkLeft.work_left_entry_steer(d, q, a, b, k, n, r, rest):
  +r7 = Wr.put_nat(k, Wr.put_nat(n, SpL.w_reading(r, rest)))
  +r6 = Wr.put_nat(2n, r7)
  +r5 = Wr.put_bool(b, r6)
  +r4 = Wr.put_bool(a, r5)
  +r3 = Wr.put_bool(q, r4)
  +r2 = Wr.put_bool(d, r3)
  -e = {Wr.err("work_left: malformed request") : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{d, r3}, Wire.wire_bool_round_trip(d, r3)) : {FWl.ffi.got(FWl.get_facts.driven(_)) == e : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r3), Wr.Got{q, r4}, Wire.wire_bool_round_trip(q, r4)) : {FWl.ffi.got(FWl.get_facts.queued(d, _)) == e : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r4), Wr.Got{a, r5}, Wire.wire_bool_round_trip(a, r5)) : {FWl.ffi.got(FWl.get_facts.acted(d, q, _)) == e : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r5), Wr.Got{b, r6}, Wire.wire_bool_round_trip(b, r6)) : {FWl.ffi.got(FWl.get_facts.funded(d, q, a, _)) == e : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r6), Wr.Got{2n, r7}, Wire.wire_nat_round_trip(2n, r7, {==})) : {FWl.ffi.got(FWl.get_facts.stall(d, q, a, b, FWl.get_stall(_))) == e : String}
  {==}
