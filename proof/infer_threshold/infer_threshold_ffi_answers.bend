# eukhe: the proof of LAW infer_threshold_ffi_answers
# Every number reads back (LWire.pw6.nat), and so do the two lists
# (LAW wire_list_round_trip); Bools and tags are closed chars; the entry
# writes the model's plan as the spec does.

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_threshold.bend as InferThreshold
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# The reply
# ---------

def gfa.over(o: M.Over, rest: String) -> {FT.put_over(o, rest) == InferThreshold.spell_over(o, rest) : String}:
  match o:
    case M.Under{}:
      {==}
    case M.Early{}:
      {==}
    case M.Blocks{}:
      {==}

def gfa.cut(c: Maybe<&2, Nat>) -> {FT.put_cut(c) == InferThreshold.spell_cut(c) : String}:
  match c:
    case None{}:
      {==}
    case Some{k}:
      {==}

def gfa.plan(p: M.Plan) -> {FT.put_plan(p) == InferThreshold.spell_plan(p) : String}:
  match p:
    case M.Plan{+o, +c}:
      %gfa.cut(c) : {FT.put_over(o, FT.put_cut(c)) == InferThreshold.spell_over(o, _) : String}
      gfa.over(o, FT.put_cut(c))

# The request, field by field
# ---------------------------

def gfa.cuts(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.cuts(on, t, w, r, m, keep, full, xs, Wr.get_list(~Nat, ~Wr.get_nat, InferThreshold.spell_nats(cuts, "")))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, cuts, "")), Wr.Got{cuts, ""}, Wire.wire_list_round_trip(cuts, "", hc)) : {FT.run(FT.get_req.cuts(on, t, w, r, m, keep, full, xs, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  gfa.plan(M.plan(on, t, w, r, m, keep, full, xs, cuts))

def gfa.sizes(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hx: {InferThreshold.nats_fit(xs) == True{} : Bool}, hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.sizes(on, t, w, r, m, keep, full, Wr.get_list(~Nat, ~Wr.get_nat, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, InferThreshold.spell_nats(cuts, ""))), Wr.Got{xs, InferThreshold.spell_nats(cuts, "")}, Wire.wire_list_round_trip(xs, InferThreshold.spell_nats(cuts, ""), hx)) : {FT.run(FT.get_req.sizes(on, t, w, r, m, keep, full, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  gfa.cuts(on, t, w, r, m, keep, full, xs, cuts, hc)

def gfa.full(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hf: {LawsBase.wire_fits(full) == True{} : Bool}, hx: {InferThreshold.nats_fit(xs) == True{} : Bool}, hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.full(on, t, w, r, m, keep, Wr.get_nat(Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, "")))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  %LWire.pw6.nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, "")), hf) : {FT.run(FT.get_req.full(on, t, w, r, m, keep, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  gfa.sizes(on, t, w, r, m, keep, full, xs, cuts, hx, hc)

def gfa.keep(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hk: {LawsBase.wire_fits(keep) == True{} : Bool}, hf: {LawsBase.wire_fits(full) == True{} : Bool}, hx: {InferThreshold.nats_fit(xs) == True{} : Bool}, hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.keep(on, t, w, r, m, Wr.get_nat(Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  %LWire.pw6.nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))), hk) : {FT.run(FT.get_req.keep(on, t, w, r, m, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  gfa.full(on, t, w, r, m, keep, full, xs, cuts, hf, hx, hc)

def gfa.m(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hm: {InferThreshold.z_fits(m) == True{} : Bool}, hk: {LawsBase.wire_fits(keep) == True{} : Bool}, hf: {LawsBase.wire_fits(full) == True{} : Bool}, hx: {InferThreshold.nats_fit(xs) == True{} : Bool}, hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z(Wr.get_nat(InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  match m:
    case M.Up{+n}:
      %LWire.pw6.nat(n, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, "")))), hm) : {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z.up(_))) == InferThreshold.spell_plan(M.plan(on, t, w, r, M.Up{n}, keep, full, xs, cuts)) : String}
      gfa.keep(on, t, w, r, M.Up{n}, keep, full, xs, cuts, hk, hf, hx, hc)
    case M.Down{+n}:
      %LWire.pw6.nat(n, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, "")))), hm) : {FT.run(FT.get_req.margin(on, t, w, r, FT.get_z.down(_))) == InferThreshold.spell_plan(M.plan(on, t, w, r, M.Down{n}, keep, full, xs, cuts)) : String}
      gfa.keep(on, t, w, r, M.Down{n}, keep, full, xs, cuts, hk, hf, hx, hc)

def gfa.r(+on: Bool, +t: Nat, +w: Nat, r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  hr: {InferThreshold.z_fits(r) == True{} : Bool}, hm: {InferThreshold.z_fits(m) == True{} : Bool}, hk: {LawsBase.wire_fits(keep) == True{} : Bool}, hf: {LawsBase.wire_fits(full) == True{} : Bool}, hx: {InferThreshold.nats_fit(xs) == True{} : Bool}, hc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.reserve(on, t, w, FT.get_z(Wr.get_nat(InferThreshold.spell_z(r, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, "")))))))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  match r:
    case M.Up{+n}:
      %LWire.pw6.nat(n, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))), hr) : {FT.run(FT.get_req.reserve(on, t, w, FT.get_z.up(_))) == InferThreshold.spell_plan(M.plan(on, t, w, M.Up{n}, m, keep, full, xs, cuts)) : String}
      gfa.m(on, t, w, M.Up{n}, m, keep, full, xs, cuts, hm, hk, hf, hx, hc)
    case M.Down{+n}:
      %LWire.pw6.nat(n, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))), hr) : {FT.run(FT.get_req.reserve(on, t, w, FT.get_z.down(_))) == InferThreshold.spell_plan(M.plan(on, t, w, M.Down{n}, m, keep, full, xs, cuts)) : String}
      gfa.m(on, t, w, M.Down{n}, m, keep, full, xs, cuts, hm, hk, hf, hx, hc)

def gfa.tw(+on: Bool, +t: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>,
  +fits: {InferThreshold.req_fits(t, w, r, m, keep, full, xs, cuts) == True{} : Bool})
  -> {FT.run(FT.get_req.tokens(on, Wr.get_nat(Wr.put_nat(t, Wr.put_nat(w, InferThreshold.spell_z(r, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))))))))) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}:
  +R7 = Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts))
  +R6 = Bool.and(LawsBase.wire_fits(full), R7)
  +R5 = Bool.and(LawsBase.wire_fits(keep), R6)
  +R4 = Bool.and(InferThreshold.z_fits(m), R5)
  +R3 = Bool.and(InferThreshold.z_fits(r), R4)
  +R2 = Bool.and(LawsBase.wire_fits(w), R3)
  +ht = LLogicBool.wr_and_l(LawsBase.wire_fits(t), R2, fits)
  +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(t), R2, fits)
  +hw = LLogicBool.wr_and_l(LawsBase.wire_fits(w), R3, h1)
  +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(w), R3, h1)
  +hr = LLogicBool.wr_and_l(InferThreshold.z_fits(r), R4, h2)
  +h3 = LLogicBool.wr_and_r(InferThreshold.z_fits(r), R4, h2)
  +hm = LLogicBool.wr_and_l(InferThreshold.z_fits(m), R5, h3)
  +h4 = LLogicBool.wr_and_r(InferThreshold.z_fits(m), R5, h3)
  +hk = LLogicBool.wr_and_l(LawsBase.wire_fits(keep), R6, h4)
  +h5 = LLogicBool.wr_and_r(LawsBase.wire_fits(keep), R6, h4)
  +hf = LLogicBool.wr_and_l(LawsBase.wire_fits(full), R7, h5)
  +h6 = LLogicBool.wr_and_r(LawsBase.wire_fits(full), R7, h5)
  +hx = LLogicBool.wr_and_l(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts), h6)
  +hc = LLogicBool.wr_and_r(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts), h6)
  +rz = InferThreshold.spell_z(r, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, ""))))))
  %LWire.pw6.nat(t, Wr.put_nat(w, rz), ht) : {FT.run(FT.get_req.tokens(on, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  %LWire.pw6.nat(w, rz, hw) : {FT.run(FT.get_req.window(on, t, _)) == InferThreshold.spell_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) : String}
  gfa.r(on, t, w, r, m, keep, full, xs, cuts, hr, hm, hk, hf, hx, hc)

def InferThreshold.infer_threshold_ffi_answers(on, t, w, r, m, keep, full, xs, cuts, fits):
  match on:
    case True{}:
      gfa.tw(True{}, t, w, r, m, keep, full, xs, cuts, fits)
    case False{}:
      gfa.tw(False{}, t, w, r, m, keep, full, xs, cuts, fits)
