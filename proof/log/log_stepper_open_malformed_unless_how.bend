# eukhe: the proof of LAW log_stepper_open_malformed_unless_how
#
# The tag that reads gives the prefix of the input (wire_nat_exact), and so
# does the Bool of a stamped open (wire_bool_exact); an unknown tag or no
# Nat or Bool answers the malformed open, which the premise refutes.

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

def lm.G(+s: String) -> Type:
  &h: Lr.How -> &rest: String -> {s == Log.log_spell_how(h, rest) : String}

def lm.kept(+s: String, +s1: String, ex: {s == Wr.put_nat(2n, s1) : String}, r: Wr.Dec<Bool>, er: {Wr.get_bool(s1) == r : Wr.Dec<Bool>}, other: {String.eq(Log.log_reply(FLg.open.go(FLg.get_how.kept(r))), Wr.err("log: malformed open")) == False{} : Bool}) -> lm.G(s):
  match r:
    case Wr.Got{+b, +rest}:
      (Lr.Stamped{b}, (rest, (%Wire.wire_bool_exact(s1, b, rest, er) : {s == Wr.put_nat(2n, _) : String}; ex)))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lm.G(s), other)

def lm.tag(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, other: {String.eq(Log.log_reply(FLg.open.go(FLg.get_how.tag(r))), Wr.err("log: malformed open")) == False{} : Bool}) -> lm.G(s):
  match r:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Lr.Unsynced{}, (s1, Wire.wire_nat_exact(s, 0n, s1, er)))
        case 1n:
          (Lr.Synced{}, (s1, Wire.wire_nat_exact(s, 1n, s1, er)))
        case 2n:
          lm.kept(s, s1, Wire.wire_nat_exact(s, 2n, s1, er), Wr.get_bool(s1), {==}, other)
        case 3n+k:
          LLogicLogic.pt.absurd(lm.G(s), other)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lm.G(s), other)

def Log.log_stepper_open_malformed_unless_how(s, other):
  lm.tag(s, Wr.get_nat(s), {==}, other)
