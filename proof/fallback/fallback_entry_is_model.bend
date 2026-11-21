# eukhe: the proof of LAW fallback_entry_is_model
#
# PROOF: a list of Nats that fits reads back whole (Wire.wire_list_round_trip)
# with nothing left; its Nats parse back to the request
# (fallback_entry_parses); the reply is the spec's spelling (LA.fbb.reply).

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/fallback.bend as Fallback
import ../base/wire.bend as LWire
import ./fallback_entry_parses.bend as PFallbackEntryParses
import ./base.bend as LA

def Fallback.fallback_entry_is_model(x, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, FFb.get_req(Fallback.fb_req(x, "")), Wr.Got{Fallback.fb_nats(x), ""}, Wire.wire_list_round_trip(Fallback.fb_nats(x), "", h)) : {FFb.ffi.got(_) == Fallback.fb_reply(Fb.choose(x)) : String}
  %Equal.sym(Maybe<&2, Fb.In>, FFb.parse(Fallback.fb_nats(x)), Some{x}, Fallback.fallback_entry_parses(x)) : {FFb.ffi.parsed(_) == Fallback.fb_reply(Fb.choose(x)) : String}
  LA.fbb.reply(Fb.choose(x))
