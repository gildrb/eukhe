# eukhe: the proof of LAW undo_entry_refuses
#
# PROOF: the entry answers either a decision, which opens with a Nat or a count (never 'E': wire_nat_not_err), or the one error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

def unf.act_ok(a: U.Act, rest: String) -> {LawsBase.wire_opens_err(FU.put_act(a, rest)) == False{} : Bool}:
  match a:
    case U.Took{}:
      Wire.wire_nat_not_err(0n, rest)
    case U.Restore{t}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(t, rest))
    case U.Refused{}:
      Wire.wire_nat_not_err(2n, rest)
    case U.Compare{t}:
      Wire.wire_nat_not_err(3n, Wr.put_nat(t, rest))
    case U.NoSnapshot{}:
      Wire.wire_nat_not_err(4n, rest)

def unf.step_ok(r: U.St & U.Act) -> {LawsBase.wire_opens_err(FU.put_step(r)) == False{} : Bool}:
  match r:
    case (st, a):
      match st:
        case U.St{l, b}:
          unf.act_ok(a, Wr.put_list(~Nat, ~Wr.put_nat, l, Wr.put_nat(FU.code_of_maybe(b), "")))

def unf.answer_ok(q: FU.Req) -> {LawsBase.wire_opens_err(FU.answer(q)) == False{} : Bool}:
  match q:
    case FU.QStep{st, e}:
      unf.step_ok(U.step(st, e))
    case FU.QFix{rows}:
      LE.dcw.fin_ok(Wr.put_list.go(~Nat, ~Wr.put_nat, FU.fix_codes(U.fixes(rows)), ""))
    case FU.QSeen{rows}:
      LE.dcw.fin_ok(Wr.put_list.go(~Nat, ~Wr.put_nat, FU.seen_codes(U.seens(rows)), ""))

def unf.refuse(d: Wr.Dec<FU.Req>, bad: {LawsBase.wire_opens_err(FU.ffi.got(d)) == True{} : Bool}) -> {FU.ffi.got(d) == Wr.err("undo: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FU.answer(q) == Wr.err("undo: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FU.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FU.answer(q)), True{}, bad), unf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Undo.undo_entry_refuses(s, bad):
  unf.refuse(FU.get_req(s), bad)
