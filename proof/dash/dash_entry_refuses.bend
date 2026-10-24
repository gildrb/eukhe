# eukhe: the proof of LAW dash_entry_refuses
#
# PROOF: the entry answers either a request's choice, which opens with a
# Nat (never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ./base.bend as LA

def df.shown(x: Da.Shown) -> {LawsBase.wire_opens_err(FDa.put_shown(x)) == False{} : Bool}:
  match x:
    case Da.Hex{bs}:
      Wire.wire_nat_not_err(0n, Wr.put_list(~Nat, ~Wr.put_nat, bs, ""))
    case Da.Blank{}:
      Wire.wire_nat_not_err(1n, "")
    case Da.Junk{}:
      Wire.wire_nat_not_err(2n, "")

def df.stored(m: Maybe<&2, List<&2, Nat>>) -> {LawsBase.wire_opens_err(FDa.put_stored(m)) == False{} : Bool}:
  match m:
    case Some{bs}:
      Wire.wire_nat_not_err(0n, Wr.put_list(~Nat, ~Wr.put_nat, bs, ""))
    case None{}:
      Wire.wire_nat_not_err(1n, "")

def df.pass(p: Da.Pass) -> {LawsBase.wire_opens_err(FDa.put_pass(p)) == False{} : Bool}:
  match p:
    case Da.Admit{}:
      Wire.wire_nat_not_err(0n, "")
    case Da.Refuse{t}:
      Wire.wire_nat_not_err(1n, Wr.put_str(t, ""))

# a request's choice is a value, never the error form
def df.answer_ok(q: FDa.Req) -> {LawsBase.wire_opens_err(FDa.answer(q)) == False{} : Bool}:
  match q:
    case FDa.QToken{t}:
      df.shown(Da.shown(t))
    case FDa.QStored{f}:
      df.stored(Da.stored(f))
    case FDa.QGate{x, f, b}:
      df.pass(Da.gate(x, f, b))
    case FDa.QFrame{f, b}:
      df.pass(Da.frame(f, b))
    case FDa.QKeep{o, f, m}:
      Wire.wire_nat_not_err(FDa.keep.tag(Da.keep(o, f, m)), "")

def df.refuse(d: Wr.Dec<FDa.Req>, bad: {LawsBase.wire_opens_err(FDa.ffi.got(d)) == True{} : Bool}) -> {FDa.ffi.got(d) == Wr.err("dash: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LA.dashboard_auth.pa.absurdT({FDa.answer(q) == Wr.err("dash: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FDa.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDa.answer(q)), True{}, bad), df.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Dash.dash_entry_refuses(s, bad):
  df.refuse(FDa.get_req(s), bad)
