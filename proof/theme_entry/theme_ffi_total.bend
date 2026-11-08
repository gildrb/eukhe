# eukhe: the proof of LAW theme_ffi_total
# The entry reads every input as the laws' reader does (LTRead.tl.req.go);
# a request read whole is answered as the laws spell its decision: a
# load's parse (LTWrite.tw.parsed), a pick (LTLoad.tv.resolve), a shipped
# table (LTWrite.tw.rgbs); anything else is the error form.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/color.bend as Co
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme/read.bend as Tr
import ../../spec/theme/wire.bend as Tw
import ../../laws/theme_entry.bend as ThemeEntry
import ../theme/base/ffi_read.bend as LTRead
import ../theme/base/ffi_write.bend as LTWrite
import ../theme/base/ffi_load.bend as LTLoad

def tt.reply(r: FTh.Req) -> {FTh.reply(r) == Tw.answer(r) : String}:
  match r:
    case FTh.Load{f}:
      LTWrite.tw.parsed(TPalette.parse(f), "")
    case FTh.Resolve{n, ss}:
      LTLoad.tv.resolve(n, ss)
    case FTh.Shipped{s}:
      %LTWrite.tw.rgbs(TBundled.table(s), "") : {Wr.put_nat(List.length(&2, Co.Rgb, TBundled.table(s)), FTh.put_rgbs.items(TBundled.table(s), "")) == Wr.put_nat(List.length(&2, Co.Rgb, TBundled.table(s)), _) : String}
      {==}

def tt.end(b: Bool, r: FTh.Req) -> {FTh.run.end(b, r) == ThemeEntry.th_entry.of(Tr.read.req.end(b, r)) : String}:
  match b:
    case True{}:
      tt.reply(r)
    case False{}:
      {==}

def tt.whole(d: Wr.Dec<FTh.Req>) -> {FTh.run(d) == ThemeEntry.th_entry.of(Tr.read.req.whole(d)) : String}:
  match d:
    case Wr.Got{r, s}:
      tt.end(Wr.end(s), r)
    case Wr.Bad{}:
      {==}

def ThemeEntry.theme_ffi_total(s):
  %LTRead.tl.req.go(Wr.get_nat(s)) : {FTh.run(_) == ThemeEntry.th_entry(s) : String}
  tt.whole(Tr.read.req.go(Wr.get_nat(s)))
