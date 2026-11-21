# eukhe: the proof of LAW fallback_entry_refuses
#
# PROOF: the entry answers either a choice, which opens with its tag (never
# 'E': Wire.wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/fallback.bend as Fallback
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def fbr.answer_ok(c: Fb.Choice) -> {LawsBase.wire_opens_err(FFb.put_choice(c)) == False{} : Bool}:
  match c:
    case Fb.Keep{}:
      Wire.wire_nat_not_err(0n, "")
    case Fb.Switch{m}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(m, ""))
    case Fb.Hold{until}:
      Wire.wire_nat_not_err(2n, Wr.put_nat(until, ""))
    case Fb.End{}:
      Wire.wire_nat_not_err(3n, "")

def fbr.parsed(r: Maybe<&2, Fb.In>, bad: {LawsBase.wire_opens_err(FFb.ffi.parsed(r)) == True{} : Bool}) -> {FFb.ffi.parsed(r) == Wr.err("fallback: malformed request") : String}:
  match r:
    case None{}:
      {==}
    case Some{+x}:
      LStg.stg.absurd({FFb.put_choice(Fb.choose(x)) == Wr.err("fallback: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FFb.put_choice(Fb.choose(x))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FFb.put_choice(Fb.choose(x))), True{}, bad), fbr.answer_ok(Fb.choose(x))))

def fbr.refuse(d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(FFb.ffi.got(d)) == True{} : Bool}) -> {FFb.ffi.got(d) == Wr.err("fallback: malformed request") : String}:
  match d:
    case Wr.Got{+xs, rest}:
      match rest:
        case SNil{}:
          fbr.parsed(FFb.parse(xs), bad)
        case SCon{c, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Fallback.fallback_entry_refuses(s, bad):
  fbr.refuse(FFb.get_req(s), bad)
