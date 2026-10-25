# eukhe: the proof of LAW wire_str_decimal
#
# PROOF of LAW wire_str_decimal: put_str is put_nat of the length before
# the chars (wr_put_str), put_nat is wire_dec (wire_nat_decimal), and the
# proofs' append is Base's String.append (wsd_app).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString

# the proofs' append is String.append
def wsd_app(a: String, -rest: String) -> {LLogicString.wr_app(a, rest) == String.append(a, rest) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %wsd_app(t, rest) : {SCon{c, LLogicString.wr_app(t, rest)} == SCon{c, _} : String}
      {==}

def Wire.wire_str_decimal(a, rest):
  +r = rest
  +l = String.length(a)
  %wsd_app(a, r) : {Wr.put_str(a, r) == LawsBase.wire_dec(l, _) : String}
  %Wire.wire_nat_decimal(l, LLogicString.wr_app(a, r)) : {Wr.put_str(a, r) == _ : String}
  LWire.wr_put_str(a, r)
