# eukhe: the proof of LAW replace_ffi_unknown_caller
#
# PROOF of LAW replace_ffi_unknown_caller: the tag 1, both versions and
# the flag read back (wire round trips); the caller tag 2 + n reads as
# itself when it fits and as Bad when too long (ws_nat_read); both ways
# the caller is Bad, so the request is malformed.

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/base/spell.bend as LAWireSpell

def rfu.caller(b: Bool, -c: String, -d: String, -same: Bool, -n: Nat, -rest: String) -> {FRp.ffi.of(FRp.get_verdict.k(c, d, same, FRp.get_caller.of(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))) == Wr.err("replace: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Replace.replace_ffi_unknown_caller(c, d, f, same, n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)))))), Wr.Got{1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest))))}, Wire.wire_nat_round_trip(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)))), {==})) : {FRp.ffi.of(FRp.get_req.of(_)) == Wr.err("replace: malformed request") : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest))))), Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)))}, Wire.wire_str_round_trip(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest))), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f))) : {FRp.ffi.of(FRp.get_verdict(_)) == Wr.err("replace: malformed request") : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)))), Wr.Got{d, Wr.put_bool(same, Wr.put_nat(2n+n, rest))}, Wire.wire_str_round_trip(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)), LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f))) : {FRp.ffi.of(FRp.get_verdict.d(c, _)) == Wr.err("replace: malformed request") : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(same, Wr.put_nat(2n+n, rest))), Wr.Got{same, Wr.put_nat(2n+n, rest)}, Wire.wire_bool_round_trip(same, Wr.put_nat(2n+n, rest))) : {FRp.ffi.of(FRp.get_verdict.same(c, d, _)) == Wr.err("replace: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FRp.ffi.of(FRp.get_verdict.k(c, d, same, FRp.get_caller.of(_))) == Wr.err("replace: malformed request") : String}
  rfu.caller(LawsBase.wire_fits(2n+n), c, d, same, n, rest)
