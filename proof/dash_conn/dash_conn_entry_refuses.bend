# eukhe: the proof of LAW dash_conn_entry_refuses
#
# PROOF: a step answers either a spelled verdict, which never opens with
# 'E' (der.reply_ok: case by case), or the malformed error with the socket
# kept; an error answer is thus the latter.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def der.verdict_ok(v: Da.Verdict) -> {LawsBase.wire_opens_err(FDa.put_verdict(v)) == False{} : Bool}:
  match v:
    case Da.VPaired{}:
      {==}
    case Da.VRun{}:
      {==}
    case Da.VRefuse{t}:
      {==}
    case Da.VClosed{}:
      {==}

def der.reply_ok(r: Da.Conn & Da.Verdict) -> {LawsBase.wire_opens_err(DashConn.cs_out(FDa.step.reply(r))) == False{} : Bool}:
  (c, v) = r
  der.verdict_ok(v)

def der.end(b: Bool, +c: Da.Conn, +e: Da.CEv, bad: {LawsBase.wire_opens_err(DashConn.cs_out(FDa.step.end(b, c, e))) == True{} : Bool}) -> {FDa.step.end(b, c, e) == (FDa.Live{c}, DashConn.sp_malformed()) : FDa.St & String}:
  match b:
    case True{}:
      LA.dcn.contra({FDa.step.end(True{}, c, e) == (FDa.Live{c}, DashConn.sp_malformed()) : FDa.St & String}, LawsBase.wire_opens_err(DashConn.cs_out(FDa.step.reply(Da.cstep(c, e)))), der.reply_ok(Da.cstep(c, e)), bad)
    case False{}:
      {==}

def der.ev(+c: Da.Conn, r: Wr.Dec<Da.CEv>, bad: {LawsBase.wire_opens_err(DashConn.cs_out(FDa.step.ev(c, r))) == True{} : Bool}) -> {FDa.step.ev(c, r) == (FDa.Live{c}, DashConn.sp_malformed()) : FDa.St & String}:
  match r:
    case Wr.Got{+e, +rest}:
      der.end(Wr.end(rest), c, e, bad)
    case Wr.Bad{}:
      {==}

def DashConn.dash_conn_entry_refuses(c, s, bad):
  der.ev(c, FDa.get_ev(s), bad)
