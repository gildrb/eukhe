# eukhe: the proof of LAW color_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that reader
# finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/color.bend as Color
import ./base.bend as LCo

def cm.end(b: Bool, -r: FCo.Req, no: {Color.co_read_req.end(b, r) == None{} : Maybe<&2, FCo.Req>}) -> {FCo.run.end(b, r) == Color.co_refused() : String}:
  match b:
    case True{}:
      LCo.ce.some_none(FCo.Req, r, {FCo.reply(r) == Color.co_refused() : String}, no)
    case False{}:
      {==}

def cm.whole(d: Wr.Dec<FCo.Req>, no: {Color.co_read_req.whole(d) == None{} : Maybe<&2, FCo.Req>}) -> {FCo.run(d) == Color.co_refused() : String}:
  match d:
    case Wr.Got{r, s}:
      cm.end(Wr.end(s), r, no)
    case Wr.Bad{}:
      {==}

def Color.color_ffi_malformed_exact(s, no):
  %LCo.ce.req(Wr.get_nat(s)) : {FCo.run(_) == Color.co_refused() : String}
  cm.whole(Color.co_read_req.go(Wr.get_nat(s)), no)
