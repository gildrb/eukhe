# eukhe: the proof of LAW cow_entry

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/sandbox.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../base/wire.bend as LWire

# Sandbox
# -------

def pw6.doc(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FSb.get_doc(FSb.put_doc(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FSb.get_doc.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FSb.get_doc.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FSb.get_doc.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def Sandbox.cow_entry(p, b, c, hp, hb, hc):
  %pw6.doc(p, FSb.put_doc(b, FSb.put_doc(c, "")), hp) : {FSb.run.p(_) == FSb.put_plan(Sb.plan(p, b, c), "") : String}
  %pw6.doc(b, FSb.put_doc(c, ""), hb) : {FSb.run.b(p, _) == FSb.put_plan(Sb.plan(p, b, c), "") : String}
  %pw6.doc(c, "", hc) : {FSb.run.c(p, b, _) == FSb.put_plan(Sb.plan(p, b, c), "") : String}
  {==}
