# eukhe: the proof of LAW autonomous_entry_refuses
#
# PROOF: the entry answers either a step, which opens with its tag (a
# Nat, never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/autonomous.bend as Autonomous
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def aur.put_ok(t: Au.Step) -> {LawsBase.wire_opens_err(FAu.put_step(t, "")) == False{} : Bool}:
  match t:
    case Au.Off{}:
      Wire.wire_nat_not_err(0n, "")
    case Au.Hold{}:
      Wire.wire_nat_not_err(1n, "")
    case Au.Continue{}:
      Wire.wire_nat_not_err(2n, "")
    case Au.Stop{c}:
      Wire.wire_nat_not_err(3n, FAu.put_cause(c, ""))

def aur.done(+f: Au.Facts, e: Bool, bad: {LawsBase.wire_opens_err(FAu.ffi.done(f, e)) == True{} : Bool}) -> {FAu.ffi.done(f, e) == Wr.err("autonomous: malformed request") : String}:
  match e:
    case True{}:
      LStg.stg.absurd({FAu.put_step(Au.decide(f), "") == Wr.err("autonomous: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FAu.put_step(Au.decide(f), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAu.put_step(Au.decide(f), "")), True{}, bad), aur.put_ok(Au.decide(f))))
    case False{}:
      {==}

def aur.refuse(d: Wr.Dec<Au.Facts>, bad: {LawsBase.wire_opens_err(FAu.ffi.got(d)) == True{} : Bool}) -> {FAu.ffi.got(d) == Wr.err("autonomous: malformed request") : String}:
  match d:
    case Wr.Got{+f, +rest}:
      aur.done(f, Wr.end(rest), bad)
    case Wr.Bad{}:
      {==}

def Autonomous.autonomous_entry_refuses(s, bad):
  aur.refuse(FAu.get_facts(s), bad)
