# eukhe: the proof of LAW log_stepper_open_reads_only_a_how
#
# The tag that reads gives the prefix of the input (wire_nat_exact), and so
# does the Bool of a stamped open (wire_bool_exact); input left over, an
# unknown tag or no Nat or Bool answers the error form, which the premise
# refutes.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact

def lr.G(s: String) -> Type:
  &h: Lr.How -> {s == Log.log_spell_how(h, "") : String}

def lr.end(rest: String, +s: String, +h: Lr.How, ex: {s == Log.log_spell_how(h, rest) : String}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.end(Wr.end(rest), h))) == False{} : Bool}) -> lr.G(s):
  match rest:
    case SNil{}:
      (h, ex)
    case SCon{c, t}:
      LLogicLogic.pt.absurd(lr.G(s), ok)

def lr.kept(+s: String, +s1: String, ex: {s == Wr.put_nat(2n, s1) : String}, r: Wr.Dec<Bool>, er: {Wr.get_bool(s1) == r : Wr.Dec<Bool>}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.go(FLg.get_how.kept(r)))) == False{} : Bool}) -> lr.G(s):
  match r:
    case Wr.Got{+b, +rest}:
      lr.end(rest, s, Lr.Stamped{b}, (%Wire.wire_bool_exact(s1, b, rest, er) : {s == Wr.put_nat(2n, _) : String}; ex), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lr.G(s), ok)

def lr.tag(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.go(FLg.get_how.tag(r)))) == False{} : Bool}) -> lr.G(s):
  match r:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          lr.end(s1, s, Lr.Unsynced{}, Wire.wire_nat_exact(s, 0n, s1, er), ok)
        case 1n:
          lr.end(s1, s, Lr.Synced{}, Wire.wire_nat_exact(s, 1n, s1, er), ok)
        case 2n:
          lr.kept(s, s1, Wire.wire_nat_exact(s, 2n, s1, er), Wr.get_bool(s1), {==}, ok)
        case 3n+k:
          LLogicLogic.pt.absurd(lr.G(s), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lr.G(s), ok)

def Log.log_stepper_open_reads_only_a_how(s, ok):
  lr.tag(s, Wr.get_nat(s), {==}, ok)
