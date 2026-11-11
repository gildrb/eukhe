# eukhe: the proof of LAW wire_entry_echoes
#
# PROOF: each field's reader reads the spec's decimal spelling back and
# leaves the rest (LAWireDec.wdec.reads_nat, wire_u32_reads_decimal,
# LAWireDec.wdec.reads_bool, wire_str_reads_decimal,
# wire_nats_reads_decimal), so the entry reads the whole request with
# nothing left and writes the values again; each writer writes the spec's
# spelling (LAWireDec.wdec.nat, LAWireDec.wdec.u32, LAWireDec.wdec.bool,
# wire_str_decimal, wire_nats_decimal).

import Base
import ../../bend/ffi_wire.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_entry.bend as WireEntry
import ../wire/wire_u32_reads_decimal.bend as PWireU32ReadsDecimal
import ../wire/wire_str_reads_decimal.bend as PWireStrReadsDecimal
import ../wire/wire_nats_reads_decimal.bend as PWireNatsReadsDecimal
import ../wire/wire_str_decimal.bend as PWireStrDecimal
import ../wire/wire_nats_decimal.bend as PWireNatsDecimal
import ../wire/base/dec.bend as LAWireDec
import ./base.bend as LAWireEntry

def WireEntry.wire_entry_echoes(n, x, b, a, xs, h):
  +hh = h
  +r4 = LawsBase.wire_dec_nats(xs, "")
  +r3 = LawsBase.wire_dec_str(a, r4)
  +r2 = {SCon{LawsBase.wire_bool_char(b), r3} : String}
  +r1 = LawsBase.wire_dec(U32.to_nat(x), r2)
  +sp = LawsBase.wire_dec(n, r1)
  +t = Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)))
  +hn = LAWireEntry.web.and_l(LawsBase.wire_fits(n), t, hh)
  +ht = LAWireEntry.web.and_r(LawsBase.wire_fits(n), t, hh)
  +ha = LAWireEntry.web.and_l(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), ht)
  +hl = LAWireEntry.web.and_r(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), ht)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(sp), Wr.Got{n, r1}, LAWireDec.wdec.reads_nat(n, r1, hn)) : {FW.at.nat(_) == sp : String}
  %Equal.sym(Wr.Dec<U32>, Wr.get_u32(r1), Wr.Got{x, r2}, Wire.wire_u32_reads_decimal(x, r2)) : {FW.at.u32(_, n) == sp : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{b, r3}, LAWireDec.wdec.reads_bool(b, r3)) : {FW.at.bool(_, n, x) == sp : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(r3), Wr.Got{a, r4}, Wire.wire_str_reads_decimal(a, r4, ha)) : {FW.at.str(_, n, x, b) == sp : String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r4), Wr.Got{xs, ""}, Wire.wire_nats_reads_decimal(xs, "", hl)) : {FW.at.end(_, n, x, b, a) == sp : String}
  %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""), r4, Wire.wire_nats_decimal(xs, "")) : {Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, _)))) == sp : String}
  %Equal.sym(String, Wr.put_str(a, r4), r3, Wire.wire_str_decimal(a, r4)) : {Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, _))) == sp : String}
  %Equal.sym(String, Wr.put_bool(b, r3), r2, LAWireDec.wdec.bool(b, r3)) : {Wr.put_nat(n, Wr.put_u32(x, _)) == sp : String}
  %Equal.sym(String, Wr.put_u32(x, r2), r1, LAWireDec.wdec.u32(x, r2)) : {Wr.put_nat(n, _) == sp : String}
  %Equal.sym(String, Wr.put_nat(n, r1), sp, LAWireDec.wdec.nat(n, r1)) : {_ == sp : String}
  {==}
