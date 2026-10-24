# eukhe: the proof of LAW infer_threshold_ffi_answers
# Every number reads back (LWire.pw6.nat); Bools and tags are closed
# chars; the entry writes the model's answer as the spec does.

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

def gfa.over(o: M.Over) -> {FT.put_over(o) == InferThreshold.spell_over(o) : String}:
  match o:
    case M.Under{}:
      {==}
    case M.Early{}:
      {==}
    case M.Blocks{}:
      {==}

def gfa.m(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, m: M.Z, hm: {InferThreshold.z_fits(m) == True{} : Bool}) -> {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z(Wr.get_nat(InferThreshold.spell_z(m, ""))))) == InferThreshold.spell_over(M.over(on, t, w, r, m)) : String}:
  match m:
    case M.Up{+n}:
      %LWire.pw6.nat(n, "", hm) : {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z.up(_))) == InferThreshold.spell_over(M.over(on, t, w, r, M.Up{n})) : String}
      gfa.over(M.over(on, t, w, r, M.Up{n}))
    case M.Down{+n}:
      %LWire.pw6.nat(n, "", hm) : {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z.down(_))) == InferThreshold.spell_over(M.over(on, t, w, r, M.Down{n})) : String}
      gfa.over(M.over(on, t, w, r, M.Down{n}))

def gfa.r(+on: Bool, +t: Nat, +w: Nat, r: M.Z, +m: M.Z, hr: {InferThreshold.z_fits(r) == True{} : Bool}, hm: {InferThreshold.z_fits(m) == True{} : Bool}) -> {FT.run(FT.get_req.reserve(on, t, w, FT.get_z(Wr.get_nat(InferThreshold.spell_z(r, InferThreshold.spell_z(m, "")))))) == InferThreshold.spell_over(M.over(on, t, w, r, m)) : String}:
  match r:
    case M.Up{+n}:
      %LWire.pw6.nat(n, InferThreshold.spell_z(m, ""), hr) : {FT.run(FT.get_req.reserve(on, t, w, FT.get_z.up(_))) == InferThreshold.spell_over(M.over(on, t, w, M.Up{n}, m)) : String}
      gfa.m(on, t, w, M.Up{n}, m, hm)
    case M.Down{+n}:
      %LWire.pw6.nat(n, InferThreshold.spell_z(m, ""), hr) : {FT.run(FT.get_req.reserve(on, t, w, FT.get_z.down(_))) == InferThreshold.spell_over(M.over(on, t, w, M.Down{n}, m)) : String}
      gfa.m(on, t, w, M.Down{n}, m, hm)

def gfa.tw(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +fits: {InferThreshold.req_fits(t, w, r, m) == True{} : Bool}) -> {FT.run(FT.get_req.tokens(on, Wr.get_nat(Wr.put_nat(t, Wr.put_nat(w, InferThreshold.spell_z(r, InferThreshold.spell_z(m, ""))))))) == InferThreshold.spell_over(M.over(on, t, w, r, m)) : String}:
  +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), InferThreshold.z_fits(m))), fits)
  +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), InferThreshold.z_fits(m)), h1)
  +ht = LLogicBool.wr_and_l(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), InferThreshold.z_fits(m))), fits)
  +hw = LLogicBool.wr_and_l(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), InferThreshold.z_fits(m)), h1)
  +hr = LLogicBool.wr_and_l(InferThreshold.z_fits(r), InferThreshold.z_fits(m), h2)
  +hm = LLogicBool.wr_and_r(InferThreshold.z_fits(r), InferThreshold.z_fits(m), h2)
  %LWire.pw6.nat(t, Wr.put_nat(w, InferThreshold.spell_z(r, InferThreshold.spell_z(m, ""))), ht) : {FT.run(FT.get_req.tokens(on, _)) == InferThreshold.spell_over(M.over(on, t, w, r, m)) : String}
  %LWire.pw6.nat(w, InferThreshold.spell_z(r, InferThreshold.spell_z(m, "")), hw) : {FT.run(FT.get_req.window(on, t, _)) == InferThreshold.spell_over(M.over(on, t, w, r, m)) : String}
  gfa.r(on, t, w, r, m, hr, hm)

def InferThreshold.infer_threshold_ffi_answers(on, t, w, r, m, fits):
  match on:
    case True{}:
      gfa.tw(True{}, t, w, r, m, fits)
    case False{}:
      gfa.tw(False{}, t, w, r, m, fits)
