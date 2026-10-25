# eukhe: the proof of LAW overflow_entry_reads
#
# PROOF: the question's tag and the stop's tag read back, then each field
# by its wire round trip (every number and length fits by the premise), so
# each stage of the decoder hands the next one exactly the rest after its
# field.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ../base/logic/bool.bend as LLogicBool

def ovr.stop(st: O.Stop, rest: String) -> {FO.get_stop(Overflow.sp_w_stop(st, rest)) == Wr.Got{st, rest} : Wr.Dec<O.Stop>}:
  match st:
    case O.SStop{}:
      {==}
    case O.SLength{}:
      {==}
    case O.SOther{}:
      {==}
    case O.SError{}:
      {==}

def ovr.req(q: FO.Req, +rest: String, h: {Overflow.sp_fit_req(q) == True{} : Bool}) -> {FO.get_req(Overflow.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FO.Req>}:
  match q:
    case FO.QOverflow{+st, +m, +p, +w, +i, +c, +o}:
      +h1 = h
      +fm = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(m)), Bool.and(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))))), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(m)), Bool.and(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))))), h1)
      +fp = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)))), h2)
      +h3 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)))), h2)
      +fw = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))), h3)
      +h4 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))), h3)
      +fi = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)), h4)
      +h5 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)), h4)
      +fc = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(c), LawsBase.wire_fits(o), h5)
      +fo = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(c), LawsBase.wire_fits(o), h5)
      +r6 = Wr.put_nat(o, rest)
      +r5 = Wr.put_nat(c, r6)
      +r4 = Wr.put_nat(i, r5)
      +r3 = Wr.put_nat(w, r4)
      +r2 = Wr.put_str(p, r3)
      +r1 = Wr.put_str(m, r2)
      %Equal.sym(Wr.Dec<O.Stop>, FO.get_stop(Overflow.sp_w_stop(st, r1)), Wr.Got{st, r1}, ovr.stop(st, r1)) : {FO.get_ov(_) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(r1), Wr.Got{m, r2}, Wire.wire_str_round_trip(m, r2, fm)) : {FO.get_ov.msg(st, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(r2), Wr.Got{p, r3}, Wire.wire_str_round_trip(p, r3, fp)) : {FO.get_ov.provider(st, m, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r3), Wr.Got{w, r4}, Wire.wire_nat_round_trip(w, r4, fw)) : {FO.get_ov.window(st, m, p, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r4), Wr.Got{i, r5}, Wire.wire_nat_round_trip(i, r5, fi)) : {FO.get_ov.input(st, m, p, w, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r5), Wr.Got{c, r6}, Wire.wire_nat_round_trip(c, r6, fc)) : {FO.get_ov.cache(st, m, p, w, i, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r6), Wr.Got{o, rest}, Wire.wire_nat_round_trip(o, rest, fo)) : {FO.get_ov.output(st, m, p, w, i, c, _) == Wr.Got{FO.QOverflow{st, m, p, w, i, c, o}, rest} : Wr.Dec<FO.Req>}
      {==}
    case FO.QRecoverable{+st, +d, +o}:
      +h1 = h
      +fd = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(d), LawsBase.wire_fits(o), h1)
      +fo = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(d), LawsBase.wire_fits(o), h1)
      +r2 = Wr.put_nat(o, rest)
      +r1 = Wr.put_nat(d, r2)
      %Equal.sym(Wr.Dec<O.Stop>, FO.get_stop(Overflow.sp_w_stop(st, r1)), Wr.Got{st, r1}, ovr.stop(st, r1)) : {FO.get_rc(_) == Wr.Got{FO.QRecoverable{st, d, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r1), Wr.Got{d, r2}, Wire.wire_nat_round_trip(d, r2, fd)) : {FO.get_rc.desired(st, _) == Wr.Got{FO.QRecoverable{st, d, o}, rest} : Wr.Dec<FO.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r2), Wr.Got{o, rest}, Wire.wire_nat_round_trip(o, rest, fo)) : {FO.get_rc.output(st, d, _) == Wr.Got{FO.QRecoverable{st, d, o}, rest} : Wr.Dec<FO.Req>}
      {==}

def Overflow.overflow_entry_reads(q, rest, h):
  ovr.req(q, rest, h)
