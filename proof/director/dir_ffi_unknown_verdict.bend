# eukhe: the proof of LAW dir_ffi_unknown_verdict
#
# PROOF: the cap reads back (wire_nat_round_trip), the spelled loop is the
# entry's own encoding of it (pds.loop) and reads back (pdf.loop_rt); the
# count reads back and is one more than a Nat (pd.add_succ); each spelled
# verdict before the unknown one reads back (pds.verdict, pdf.verdict_rt),
# and a verdict tag of 7 or more reads as itself, or as Bad when too long
# (ws_nat_read): Bad both ways, so the list decoder answers Bad (pduv.go,
# by induction on the verdicts before it).

import Base
import ../../bend/director.bend as Dr
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/base/spell.bend as LAWireSpell
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LA
import ./dir_ffi_answers_spelled/spell.bend as LS

def pduv.ans(b: Bool, +n: Nat, +rest: String) -> {FDr.get_verdict.go(LAWireSpell.ws_nat_answer(b, 7n+n, rest)) == Wr.Bad{} : Wr.Dec<Dr.Verdict>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a verdict tag of 7 or more is Bad
def pduv.bad(+n: Nat, +rest: String) -> {FDr.get_verdict(Wr.put_nat(7n+n, rest)) == Wr.Bad{} : Wr.Dec<Dr.Verdict>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(7n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(7n+n), 7n+n, rest), LAWireSpell.ws_nat_read(7n+n, rest)) : {FDr.get_verdict.go(_) == Wr.Bad{} : Wr.Dec<Dr.Verdict>}
  pduv.ans(LawsBase.wire_fits(7n+n), n, rest)

# the item loop on a Bad item is Bad
def pduv.none(m: Nat) -> {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, m, Wr.Bad{}) == Wr.Bad{} : Wr.Dec<List<&2, Dr.Verdict>>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

# a spelled verdict that fits reads back
def pduv.verdict_rt(+x: Dr.Verdict, +r: String, h: {Director.dir_verdict_fits(x) == True{} : Bool}) -> {FDr.get_verdict(Director.dir_spell_verdict(x, r)) == Wr.Got{x, r} : Wr.Dec<Dr.Verdict>}:
  %LS.pds.verdict(x, r) : {FDr.get_verdict(_) == Wr.Got{x, r} : Wr.Dec<Dr.Verdict>}
  LA.pdf.verdict_rt(x, r, h)

# the item loop over the spelled verdicts vs, then the unknown tag, is Bad
# for every count of at least as many items
def pduv.go(vs: List<&2, Dr.Verdict>, +m: Nat, +n: Nat, +rest: String, h: {Director.dir_verdicts_fit(vs) == True{} : Bool}) -> {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, Nat.add(List.length(&2, Dr.Verdict, vs), m), FDr.get_verdict(Director.dir_spell_verdicts.items(vs, Wr.put_nat(7n+n, rest)))) == Wr.Bad{} : Wr.Dec<List<&2, Dr.Verdict>>}:
  match vs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dr.Verdict>, FDr.get_verdict(Wr.put_nat(7n+n, rest)), Wr.Bad{}, pduv.bad(n, rest)) : {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, m, _) == Wr.Bad{} : Wr.Dec<List<&2, Dr.Verdict>>}
      pduv.none(m)
    case Con{+x, +t}:
      +hh = h
      +r = Director.dir_spell_verdicts.items(t, Wr.put_nat(7n+n, rest))
      %Equal.sym(Wr.Dec<Dr.Verdict>, FDr.get_verdict(Director.dir_spell_verdict(x, r)), Wr.Got{x, r}, pduv.verdict_rt(x, r, LLogicBool.wr_and_l(Director.dir_verdict_fits(x), Director.dir_verdicts_fit(t), hh))) : {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, 1n+Nat.add(List.length(&2, Dr.Verdict, t), m), _) == Wr.Bad{} : Wr.Dec<List<&2, Dr.Verdict>>}
      %Equal.sym(Wr.Dec<List<&2, Dr.Verdict>>, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, Nat.add(List.length(&2, Dr.Verdict, t), m), FDr.get_verdict(r)), Wr.Bad{}, pduv.go(t, m, n, rest, LLogicBool.wr_and_r(Director.dir_verdict_fits(x), Director.dir_verdicts_fit(t), hh))) : {Wr.get_list.cons(Dr.Verdict, x, _) == Wr.Bad{} : Wr.Dec<List<&2, Dr.Verdict>>}
      {==}

def Director.dir_ffi_unknown_verdict(c, l, vs, m, fits, n, rest):
  +h = fits
  +ha = LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(c), Director.dir_loop_fits(l)), Bool.and(LawsBase.wire_fits(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)), Director.dir_verdicts_fit(vs)), h)
  +hb = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(c), Director.dir_loop_fits(l)), Bool.and(LawsBase.wire_fits(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)), Director.dir_verdicts_fit(vs)), h)
  +fc = LLogicBool.wr_and_l(LawsBase.wire_fits(c), Director.dir_loop_fits(l), ha)
  +fl = LLogicBool.wr_and_r(LawsBase.wire_fits(c), Director.dir_loop_fits(l), ha)
  +fn = LLogicBool.wr_and_l(LawsBase.wire_fits(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)), Director.dir_verdicts_fit(vs), hb)
  +fv = LLogicBool.wr_and_r(LawsBase.wire_fits(Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)), Director.dir_verdicts_fit(vs), hb)
  +k = Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m)
  +its = Director.dir_spell_verdicts.items(vs, Wr.put_nat(7n+n, rest))
  +v = Wr.put_nat(k, its)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(c, Director.dir_spell_loop(l, v))), Wr.Got{c, Director.dir_spell_loop(l, v)}, Wire.wire_nat_round_trip(c, Director.dir_spell_loop(l, v), fc)) : {FDr.ffi.go(FDr.get_req.cap(_)) == Wr.err("director: malformed request") : String}
  %LS.pds.loop(l, v) : {FDr.ffi.go(FDr.get_req.loop(c, FDr.get_loop(_))) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<Dr.Loop>, FDr.get_loop(FDr.put_loop(l, v)), Wr.Got{l, v}, LA.pdf.loop_rt(l, v, fl)) : {FDr.ffi.go(FDr.get_req.loop(c, _)) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(v), Wr.Got{k, its}, Wire.wire_nat_round_trip(k, its, fn)) : {FDr.ffi.go(FDr.get_req.vs(c, l, Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, _))) == Wr.err("director: malformed request") : String}
  %Equal.sym(Nat, Nat.add(List.length(&2, Dr.Verdict, vs), 1n+m), 1n+Nat.add(List.length(&2, Dr.Verdict, vs), m), LA.pd.add_succ(List.length(&2, Dr.Verdict, vs), m)) : {FDr.ffi.go(FDr.get_req.vs(c, l, Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, Wr.Got{_, its}))) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, Dr.Verdict>>, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, Nat.add(List.length(&2, Dr.Verdict, vs), m), FDr.get_verdict(its)), Wr.Bad{}, pduv.go(vs, m, n, rest, fv)) : {FDr.ffi.go(FDr.get_req.vs(c, l, _)) == Wr.err("director: malformed request") : String}
  {==}
