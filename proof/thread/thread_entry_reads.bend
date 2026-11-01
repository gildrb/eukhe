# eukhe: the proof of LAW thread_entry_reads
#
# PROOF: the spelled request is the list encoder's spelling of through,
# verbatim and the starts (wire_nats_spells), which reads back whole by
# the list round trip (wire_list_round_trip; it fits by the premise); a
# list of at least two Nats is the request.

import Base
import ../../bend/ffi_thread.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/thread.bend as Thread
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base/wire.bend as PWireBase

def ter.req(q: FTh.Req, +rest: String, h: {Thread.sp_fit_req(q) == True{} : Bool}) -> {FTh.get_req(Thread.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTh.Req>}:
  match q:
    case FTh.Req{+t, +v, +xs}:
      %Wire.wire_nats_spells(t <> v <> xs, rest) : {FTh.get_req.got(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FTh.Req{t, v, xs}, rest} : Wr.Dec<FTh.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, t <> v <> xs, rest)), Wr.Got{t <> v <> xs, rest}, Wire.wire_list_round_trip(t <> v <> xs, rest, h)) : {FTh.get_req.got(_) == Wr.Got{FTh.Req{t, v, xs}, rest} : Wr.Dec<FTh.Req>}
      {==}

def Thread.thread_entry_reads(q, rest, h):
  ter.req(q, rest, h)
