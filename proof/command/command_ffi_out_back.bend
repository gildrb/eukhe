# eukhe: the proof of LAW command_ffi_out_back
#
# PROOF of LAW command_ffi_out_back: a key reply is its line, then two
# Bools. When the length of the line fits, the round trip reads it back
# (command_ffi_out_round_trip); when it does not, the reader reads that
# length first and refuses it (Wire.wire_nat_too_long), so the whole
# reply is no reply.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ./command_ffi_out_round_trip.bend as PCommandFfiOutRoundTrip

# a string whose length is past the wire reads as no string
def cob_str_long(+a: String, +r: String, h: {LawsBase.wire_fits(String.length(a)) == False{} : Bool}) -> {Wr.get_str(Wr.put_str(a, r)) == Wr.Bad{} : Wr.Dec<String>}:
  %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), LLogicString.wr_app(a, r)), LWire.wr_put_str(a, r)) : {Wr.get_str(_) == Wr.Bad{} : Wr.Dec<String>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(String.length(a), LLogicString.wr_app(a, r))), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), LLogicString.wr_app(a, r), h)) : {Wr.get_str.go(_) == Wr.Bad{} : Wr.Dec<String>}
  {==}

def cob_go(+l: String, +a: Bool, +b: Bool, +rest: String, f: Bool, +e: {LawsBase.wire_fits(String.length(l)) == f : Bool}) -> {FCmd.get_out(FCmd.put_out(FCmd.OutW{l, a, b}, rest)) == Command.cmd_out_back(FCmd.OutW{l, a, b}, rest) : Wr.Dec<FCmd.OutW>}:
  match f:
    case True{}:
      %Equal.sym(Bool, LawsBase.wire_fits(String.length(l)), True{}, e) : {FCmd.get_out(FCmd.put_out(FCmd.OutW{l, a, b}, rest)) == Bool.pick(Wr.Dec<FCmd.OutW>, _, Wr.Got{FCmd.OutW{l, a, b}, rest}, Wr.Bad{}) : Wr.Dec<FCmd.OutW>}
      Command.command_ffi_out_round_trip(FCmd.OutW{l, a, b}, rest, e)
    case False{}:
      %Equal.sym(Bool, LawsBase.wire_fits(String.length(l)), False{}, e) : {FCmd.get_out(FCmd.put_out(FCmd.OutW{l, a, b}, rest)) == Bool.pick(Wr.Dec<FCmd.OutW>, _, Wr.Got{FCmd.OutW{l, a, b}, rest}, Wr.Bad{}) : Wr.Dec<FCmd.OutW>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(l, Wr.put_bool(a, Wr.put_bool(b, rest)))), Wr.Bad{}, cob_str_long(l, Wr.put_bool(a, Wr.put_bool(b, rest)), e)) : {FCmd.get_out.line(_) == Wr.Bad{} : Wr.Dec<FCmd.OutW>}
      {==}

def Command.command_ffi_out_back(x, rest):
  match x:
    case FCmd.OutW{+l, +a, +b}:
      cob_go(l, a, b, rest, LawsBase.wire_fits(String.length(l)), {==})
