# eukhe: the proof of LAW dash_rejected_runs_nothing
#
# PROOF: a reply that opens with '2' is no malformed error (it opens with
# 'E') and no other verdict (they open with '0', '1', '3'), so the input
# was an event whose verdict is a refusal (drj.verdict); a refusal closes
# the socket (dash_conn_refusal_closes), and a closed socket runs nothing
# (dash_closed_runs_nothing).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_refusal_closes.bend as PDashConnRefusalCloses
import ./dash_closed_runs_nothing.bend as PDashClosedRunsNothing
import ./base.bend as LA

# a reply opens with '2' (tag 2: a refusal)
def drj.two(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, r}:
      Char.is_eq(c, '2')

# a reply that does not open with '2' is no refusal
def drj.not_two(-A: Type, +s: String, +t: String, n: {drj.two(s) == False{} : Bool}, h: {s == Wr.put_nat(2n, Wr.put_str(t, "")) : String}) -> A:
  LA.dcn.contra(A, drj.two(s), n, Equal.cong(String, Bool, z => drj.two(z), s, Wr.put_nat(2n, Wr.put_str(t, "")), h))

# a verdict spelled as a refusal is one
def drj.verdict(v: Da.Verdict, +t: String, h: {FDa.put_verdict(v) == Wr.put_nat(2n, Wr.put_str(t, "")) : String}) -> {DashConn.cv_is_refuse(v) == True{} : Bool}:
  match v:
    case Da.VPaired{}:
      drj.not_two({False{} == True{} : Bool}, FDa.put_verdict(Da.VPaired{}), t, {==}, h)
    case Da.VRun{}:
      drj.not_two({False{} == True{} : Bool}, FDa.put_verdict(Da.VRun{}), t, {==}, h)
    case Da.VRefuse{x}:
      {==}
    case Da.VClosed{}:
      drj.not_two({False{} == True{} : Bool}, FDa.put_verdict(Da.VClosed{}), t, {==}, h)

def drj.reply(r: Da.Conn & Da.Verdict, +t: String, h: {DashConn.cs_out(FDa.step.reply(r)) == Wr.put_nat(2n, Wr.put_str(t, "")) : String}) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(r)) == True{} : Bool}:
  (c, v) = r
  drj.verdict(v, t, h)

def drj.conn(c: Da.Conn, v: Da.Verdict, h: {DashConn.cv_is_closed(c) == True{} : Bool}) -> {DashConn.cs_st(FDa.step.reply((c, v))) == FDa.Live{Da.Closed{}} : FDa.St}:
  match c:
    case Da.Waiting{}:
      LA.dcn.absurdF({DashConn.cs_st(FDa.step.reply((Da.Waiting{}, v))) == FDa.Live{Da.Closed{}} : FDa.St}, h)
    case Da.Paired{}:
      LA.dcn.absurdF({DashConn.cs_st(FDa.step.reply((Da.Paired{}, v))) == FDa.Live{Da.Closed{}} : FDa.St}, h)
    case Da.Closed{}:
      {==}

# a closed model socket is a closed shipped socket
def drj.closed(r: Da.Conn & Da.Verdict, h: {DashConn.cv_is_closed(DashConn.cv_conn(r)) == True{} : Bool}) -> {DashConn.cs_st(FDa.step.reply(r)) == FDa.Live{Da.Closed{}} : FDa.St}:
  (c, v) = r
  drj.conn(c, v, h)

def drj.end(b: Bool, +c: Da.Conn, +e: Da.CEv, +t: String, h: {DashConn.cs_out(FDa.step.end(b, c, e)) == Wr.put_nat(2n, Wr.put_str(t, "")) : String}) -> {DashConn.cs_st(FDa.step.end(b, c, e)) == FDa.Live{Da.Closed{}} : FDa.St}:
  match b:
    case True{}:
      drj.closed(Da.cstep(c, e), DashConn.dash_conn_refusal_closes(c, e, drj.reply(Da.cstep(c, e), t, h)))
    case False{}:
      drj.not_two({FDa.Live{c} == FDa.Live{Da.Closed{}} : FDa.St}, DashConn.sp_malformed(), t, {==}, h)

# a step answered with a refusal leaves the socket closed
def drj.ev(+c: Da.Conn, r: Wr.Dec<Da.CEv>, +t: String, h: {DashConn.cs_out(FDa.step.ev(c, r)) == Wr.put_nat(2n, Wr.put_str(t, "")) : String}) -> {DashConn.cs_st(FDa.step.ev(c, r)) == FDa.Live{Da.Closed{}} : FDa.St}:
  match r:
    case Wr.Got{+e, +rest}:
      drj.end(Wr.end(rest), c, e, t, h)
    case Wr.Bad{}:
      drj.not_two({FDa.Live{c} == FDa.Live{Da.Closed{}} : FDa.St}, DashConn.sp_malformed(), t, {==}, h)

def DashConn.dash_rejected_runs_nothing(c, s, t, ins, refused):
  %Equal.sym(FDa.St, DashConn.cs_st(FDa.step(FDa.Live{c}, s)), FDa.Live{Da.Closed{}}, drj.ev(c, FDa.get_ev(s), t, refused)) : {DashConn.cw_quiet(DashConn.cs_outs(ins, _)) == True{} : Bool}
  DashConn.dash_closed_runs_nothing(ins)
