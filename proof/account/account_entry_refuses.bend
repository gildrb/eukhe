# eukhe: the proof of LAW account_entry_refuses
#
# PROOF: the entry answers either a choice, which opens with its tag (never
# 'E': Wire.wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/account.bend as Ac
import ../../bend/ffi_account.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/account.bend as Account
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def acr.answer_ok(c: Ac.Choice) -> {LawsBase.wire_opens_err(FAc.put_choice(c)) == False{} : Bool}:
  match c:
    case Ac.Use{a}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(a, ""))
    case Ac.Hold{a, until}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(a, Wr.put_nat(until, "")))
    case Ac.Quota{a, until}:
      Wire.wire_nat_not_err(2n, Wr.put_nat(a, Wr.put_nat(until, "")))
    case Ac.Login{}:
      Wire.wire_nat_not_err(3n, "")

def acr.parsed(r: Maybe<&2, Ac.In>, bad: {LawsBase.wire_opens_err(FAc.ffi.parsed(r)) == True{} : Bool}) -> {FAc.ffi.parsed(r) == Wr.err("account: malformed request") : String}:
  match r:
    case None{}:
      {==}
    case Some{+x}:
      LStg.stg.absurd({FAc.put_choice(Ac.choose(x)) == Wr.err("account: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FAc.put_choice(Ac.choose(x))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAc.put_choice(Ac.choose(x))), True{}, bad), acr.answer_ok(Ac.choose(x))))

def acr.refuse(d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(FAc.ffi.got(d)) == True{} : Bool}) -> {FAc.ffi.got(d) == Wr.err("account: malformed request") : String}:
  match d:
    case Wr.Got{+xs, rest}:
      match rest:
        case SNil{}:
          acr.parsed(FAc.parse(xs), bad)
        case SCon{c, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Account.account_entry_refuses(s, bad):
  acr.refuse(FAc.get_req(s), bad)
