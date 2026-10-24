# eukhe: the proof of LAW command_ffi_out_round_trip
#
# PROOF of LAW command_ffi_out_round_trip: a key reply is its line (a
# string that fits, wire_str_round_trip) and two Bools
# (wire_bool_round_trip); each reads back, leaving rest.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command/entry.bend as Command
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def Command.command_ffi_out_round_trip(x, rest, h):
  match x:
    case FCmd.OutW{+l, +a, +b}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(l, Wr.put_bool(a, Wr.put_bool(b, rest)))), Wr.Got{l, Wr.put_bool(a, Wr.put_bool(b, rest))}, Wire.wire_str_round_trip(l, Wr.put_bool(a, Wr.put_bool(b, rest)), h)) : {FCmd.get_out.line(_) == Wr.Got{FCmd.OutW{l, a, b}, rest} : Wr.Dec<FCmd.OutW>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(a, Wr.put_bool(b, rest))), Wr.Got{a, Wr.put_bool(b, rest)}, Wire.wire_bool_round_trip(a, Wr.put_bool(b, rest))) : {FCmd.get_out.open(l, _) == Wr.Got{FCmd.OutW{l, a, b}, rest} : Wr.Dec<FCmd.OutW>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest)) : {FCmd.get_out.submit(l, a, _) == Wr.Got{FCmd.OutW{l, a, b}, rest} : Wr.Dec<FCmd.OutW>}
      {==}
