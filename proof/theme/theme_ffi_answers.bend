# eukhe: the proof of LAW theme_ffi_answers
# The request reads back whole (LTTrip.tt.req: the wire's round trips);
# a load's parse and a shipped table are written as the laws spell them
# (LTWrite), and one load of the model is the laws' load, spelled alike
# (LTLoad.tv.resolve).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/theme/resolve.bend as TResolve
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme_wire.bend as Tw
import ../../laws/theme.bend as Theme
import ./base/ffi_trip.bend as LTTrip
import ./base/ffi_write.bend as LTWrite
import ./base/ffi_load.bend as LTLoad

def ta.load(+f: TFile.RFile, +fits: {Tw.fits(FTh.Load{f}) == True{} : Bool}) -> {FTh.ffi(Tw.req(FTh.Load{f}, "")) == Tw.answer(FTh.Load{f}) : String}:
  %LTTrip.tt.req(FTh.Load{f}, "", fits) : {FTh.run(_) == Tw.answer(FTh.Load{f}) : String}
  LTWrite.tw.parsed(TPalette.parse(f), "")

def ta.resolve(+n: String, +ss: List<&2, TResolve.Src>, +fits: {Tw.fits(FTh.Resolve{n, ss}) == True{} : Bool}) -> {FTh.ffi(Tw.req(FTh.Resolve{n, ss}, "")) == Tw.answer(FTh.Resolve{n, ss}) : String}:
  %LTTrip.tt.req(FTh.Resolve{n, ss}, "", fits) : {FTh.run(_) == Tw.answer(FTh.Resolve{n, ss}) : String}
  LTLoad.tv.resolve(n, ss)

def ta.shipped(+s: TBundled.Shipped, +fits: {Tw.fits(FTh.Shipped{s}) == True{} : Bool}) -> {FTh.ffi(Tw.req(FTh.Shipped{s}, "")) == Tw.answer(FTh.Shipped{s}) : String}:
  %LTTrip.tt.req(FTh.Shipped{s}, "", fits) : {FTh.run(_) == Tw.answer(FTh.Shipped{s}) : String}
  %LTWrite.tw.rgbs(TBundled.table(s), "") : {Wr.put_nat(List.length(&2, Co.Rgb, TBundled.table(s)), FTh.put_rgbs.items(TBundled.table(s), "")) == Wr.put_nat(List.length(&2, Co.Rgb, TBundled.table(s)), _) : String}
  {==}

def Theme.theme_ffi_answers(r, fits):
  match r:
    case FTh.Load{f}:
      ta.load(f, fits)
    case FTh.Resolve{n, ss}:
      ta.resolve(n, ss, fits)
    case FTh.Shipped{s}:
      ta.shipped(s, fits)
