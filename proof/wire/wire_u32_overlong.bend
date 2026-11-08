# eukhe: the proof of LAW wire_u32_overlong

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./wire_nat_overlong.bend as PWireNatOverlong

def Wire.wire_u32_overlong(ds, rest, h):
  +r = rest
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(LawsBase.wire_digit_chars(ds, r)), Wr.Bad{}, Wire.wire_nat_overlong(ds, r, h)) : {Wr.get_u32.fit(_) == Wr.Bad{} : Wr.Dec<U32>}
  {==}
