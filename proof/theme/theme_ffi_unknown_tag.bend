# eukhe: the proof of LAW theme_ffi_unknown_tag
# The tag reads back (wire_nat_round_trip); the entry knows the tags 0, 1
# and 2 only, and refuses any other whatever follows it.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_theme.bend as FTh
import ../../laws/wire.bend as Wire
import ../../laws/theme.bend as Theme
import ./base.bend as LA
import ../base/wire.bend as LWire

def pu.tag(k: Nat, rest: String, big: {Nat.is_le(3n, k) == True{} : Bool}) -> {FTh.run(FTh.get_req.tag(k, rest)) == "E theme: malformed request" : String}:
  match k:
    case 0n:
      LA.themes.pt.absurdF({FTh.run(FTh.get_req.tag(0n, rest)) == "E theme: malformed request" : String}, big)
    case 1n:
      LA.themes.pt.absurdF({FTh.run(FTh.get_req.tag(1n, rest)) == "E theme: malformed request" : String}, big)
    case 2n:
      LA.themes.pt.absurdF({FTh.run(FTh.get_req.tag(2n, rest)) == "E theme: malformed request" : String}, big)
    case 3n+p:
      {==}

def Theme.theme_ffi_unknown_tag(k, rest, big, fits):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, fits)) : {FTh.run(FTh.get_req.go(_)) == "E theme: malformed request" : String}
  pu.tag(k, rest, big)
