# eukhe: the proof of LAW dir_ffi_unknown_out
#
# PROOF: the cap, the steps left and the stack read back as in
# dir_ffi_unknown_end; the end tag 1 reads back, and an outcome tag of 3
# or more reads as itself, or as Bad when too long (ws_nat_read): the
# outcome decoder answers Bad both ways.

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

def pduo.ans(b: Bool, +n: Nat, +rest: String) -> {FDr.get_end.some(LAWireSpell.ws_nat_answer(b, 3n+n, rest)) == Wr.Bad{} : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# an ended loop with an outcome tag of 3 or more is Bad
def pduo.bad(+n: Nat, +rest: String) -> {FDr.get_end(Wr.put_nat(1n, Wr.put_nat(3n+n, rest))) == Wr.Bad{} : Wr.Dec<Maybe<&2, Dr.Out>>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(3n+n, rest))), Wr.Got{1n, Wr.put_nat(3n+n, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_nat(3n+n, rest), {==})) : {FDr.get_end.go(_) == Wr.Bad{} : Wr.Dec<Maybe<&2, Dr.Out>>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {FDr.get_end.some(_) == Wr.Bad{} : Wr.Dec<Maybe<&2, Dr.Out>>}
  pduo.ans(LawsBase.wire_fits(3n+n), n, rest)

def Director.dir_ffi_unknown_out(c, left, s, fits, n, rest):
  +h = fits
  +fc = LLogicBool.wr_and_l(LawsBase.wire_fits(c), Director.dir_loop_fits(Dr.Loop{left, s, None{}}), h)
  +fl = LLogicBool.wr_and_r(LawsBase.wire_fits(c), Director.dir_loop_fits(Dr.Loop{left, s, None{}}), h)
  +fn = LLogicBool.wr_and_l(LawsBase.wire_fits(left), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, s)), Director.dir_layers_fit(s)), fl)
  +fs = LLogicBool.wr_and_r(LawsBase.wire_fits(left), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, s)), Director.dir_layers_fit(s)), fl)
  +z = Wr.put_nat(1n, Wr.put_nat(3n+n, rest))
  +y = Director.dir_spell_layers(s, z)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(c, Wr.put_nat(left, y))), Wr.Got{c, Wr.put_nat(left, y)}, Wire.wire_nat_round_trip(c, Wr.put_nat(left, y), fc)) : {FDr.ffi.go(FDr.get_req.cap(_)) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(left, y)), Wr.Got{left, y}, Wire.wire_nat_round_trip(left, y, fn)) : {FDr.ffi.go(FDr.get_req.loop(c, FDr.get_loop.left(_))) == Wr.err("director: malformed request") : String}
  %LS.pds.layers(s, z) : {FDr.ffi.go(FDr.get_req.loop(c, FDr.get_loop.stack(left, Wr.get_list(~Dr.Layer, ~FDr.get_layer, _)))) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, Dr.Layer>>, Wr.get_list(~Dr.Layer, ~FDr.get_layer, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, z)), Wr.Got{s, z}, LA.pdf.ls.rt(s, z, fs)) : {FDr.ffi.go(FDr.get_req.loop(c, FDr.get_loop.stack(left, _))) == Wr.err("director: malformed request") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Dr.Out>>, FDr.get_end(z), Wr.Bad{}, pduo.bad(n, rest)) : {FDr.ffi.go(FDr.get_req.loop(c, FDr.get_loop.end(left, s, _))) == Wr.err("director: malformed request") : String}
  {==}
