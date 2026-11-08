# eukhe: the proof of LAW tui_color_ffi_total
# The entry reads every input as the laws' reader does (LA.tcf.req); a
# request read whole is answered as tc_reply spells it: the ramp's range
# test is ramp_in, its rungs the spec's list (LA.tcf.rungs); the band is
# the model's (FB.fb.band_go), which is band_spec (tui_usage_band_exact);
# the roles compute.

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA
import ./tui_color_ffi_band.bend as FB
import ./tui_usage_band_exact.bend as UB

def tot.ramp(b: Bool, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> {FTC.answer.ramp(b, lo, hi, n) == TuiColor.tc_reply.ramp(b, lo, hi, n) : String}:
  match b:
    case True{}:
      LA.tcf.rungs(TC.ramp(lo, hi, n))
    case False{}:
      {==}

def tot.answer(q: FTC.Req) -> {FTC.answer(q) == TuiColor.tc_reply(q) : String}:
  match q:
    case FTC.QRamp{lo, hi, +n}:
      match lo hi:
        case TC.Px{+lr, +lg, +lb} TC.Px{+hr, +hg, +hb}:
          tot.ramp(TuiColor.ramp_in(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)
    case FTC.QBand{+t, +w}:
      %TuiColor.tui_usage_band_exact(t, w) : {Wr.put_nat(FTC.band(t, w), "") == Wr.put_nat(_, "") : String}
      %FB.fb.band_go(TC.bands(), t, w) : {Wr.put_nat(FTC.band.go(TC.bands(), t, w), "") == Wr.put_nat(_, "") : String}
      {==}
    case FTC.QRoles{}:
      {==}

def tot.end(b: Bool, q: FTC.Req) -> {FTC.run.end(b, q) == TuiColor.tc_entry.of(TuiColor.read_req.end(b, q)) : String}:
  match b:
    case True{}:
      tot.answer(q)
    case False{}:
      {==}

def tot.whole(r: Wr.Dec<FTC.Req>) -> {FTC.run(r) == TuiColor.tc_entry.of(TuiColor.read_req.whole(r)) : String}:
  match r:
    case Wr.Got{q, s}:
      tot.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def TuiColor.tui_color_ffi_total(s):
  %LA.tcf.req(Wr.get_nat(s)) : {FTC.run(_) == TuiColor.tc_entry(s) : String}
  tot.whole(TuiColor.read_req.go(Wr.get_nat(s)))
