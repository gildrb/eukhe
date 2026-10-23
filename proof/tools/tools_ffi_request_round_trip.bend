# eukhe: the proof of LAW tools_ffi_request_round_trip

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tools.bend as Tools
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

# tools
# -----

def fe.segs_codes(gs: List<&2, Tl.Seg>) -> {FTl.segs(FTl.codes(gs)) == gs : List<&2, Tl.Seg>}:
  match gs:
    case Nil{}:
      {==}
    case g <> +rest:
      match g:
        case Tl.Up{}:
          %fe.segs_codes(rest) : {Tl.Up{} <> FTl.segs(FTl.codes(rest)) == Tl.Up{} <> _ : List<&2, Tl.Seg>}
          {==}
        case Tl.Here{}:
          %fe.segs_codes(rest) : {Tl.Here{} <> FTl.segs(FTl.codes(rest)) == Tl.Here{} <> _ : List<&2, Tl.Seg>}
          {==}
        case Tl.Name{+n}:
          %fe.segs_codes(rest) : {Tl.Name{n} <> FTl.segs(FTl.codes(rest)) == Tl.Name{n} <> _ : List<&2, Tl.Seg>}
          {==}

def Tools.tools_ffi_request_round_trip(gs, rest, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, FTl.codes(gs), rest)), Wr.Got{FTl.codes(gs), rest}, Wire.wire_list_round_trip(FTl.codes(gs), rest, h)) : {FTl.get_req.of(_) == Wr.Got{gs, rest} : Wr.Dec<List<&2, Tl.Seg>>}
  %Equal.sym(List<&2, Tl.Seg>, FTl.segs(FTl.codes(gs)), gs, fe.segs_codes(gs)) : {Wr.Got{_, rest} == Wr.Got{gs, rest} : Wr.Dec<List<&2, Tl.Seg>>}
  {==}
