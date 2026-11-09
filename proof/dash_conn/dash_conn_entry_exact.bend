# eukhe: the proof of LAW dash_conn_entry_exact
#
# PROOF: each stage of the shipped decoder answers Got{x, rest} only for an
# input that is Rust's spelling of x before rest, with x within the wire
# (the primitives' predicates dx.* of proof/dash/dash_entry_exact.bend,
# from the wire's exactness laws; dce.*: the first frame, the Bool, the
# event). The step answers a verdict only for an event read whole with
# nothing left: that input is the spelled event (dce.top).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA
import ../../laws/wire.bend as Wire
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../dash/dash_entry_exact.bend as PDx

def dce.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# First frames
# ------------

def dce.FP(s: String, d: Wr.Dec<Da.First>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Dash.sp_w_first(x, r) : String} & {Dash.sp_fit_first(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dce.first.pair(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Da.Said>, sp: PDx.dx.SdP(s1, d)) -> dce.FP(s, FDa.get_first.pair(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (PDx.dx.after(s, 2n, s1, Dash.sp_w_said(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dce.first.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dce.FP(s, FDa.get_first.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      dce.first.pair(s, s1, pre, FDa.get_said(Wr.get_nat(s1)), PDx.dx.said(s1))
    case 3n+u:
      Unit{}

def dce.first.go(-s: String, d: Wr.Dec<Nat>, np: PDx.dx.NP(s, d)) -> dce.FP(s, FDa.get_first(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dce.first.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dce.first(+s: String) -> dce.FP(s, FDa.get_first(Wr.get_nat(s))):
  dce.first.go(s, Wr.get_nat(s), PDx.dx.nat(s))

# Bools
# -----

def dce.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def dce.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> dce.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def dce.bool(+s: String) -> dce.BP(s, Wr.get_bool(s)):
  dce.bool.at(s, Wr.get_bool(s), {==})

# Events
# ------

def dce.EP(s: String, d: Wr.Dec<Da.CEv>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == DashConn.sp_w_ev(e, r) : String} & {DashConn.sp_fit_ev(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dce.matches(-s: String, +x: Da.First, +f: Da.Disk, -s3: String, pre: {s == Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, s3))) : String}, fit: {Bool.and(Dash.sp_fit_first(x), Dash.sp_fit_disk(f)) == True{} : Bool}, d: Wr.Dec<Bool>, bp: dce.BP(s3, d)) -> dce.EP(s, FDa.get_ev.matches(x, f, d)):
  match d:
    case Wr.Got{+m, +r}:
      (Equal.trans(String, s, Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, s3))), Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, Wr.put_bool(m, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, z))), s3, Wr.put_bool(m, r), bp)), fit)
    case Wr.Bad{}:
      Unit{}

def dce.ev.first(-s: String, +x: Da.First, -s2: String, pre: {s == Wr.put_nat(0n, Dash.sp_w_first(x, s2)) : String}, fx: {Dash.sp_fit_first(x) == True{} : Bool}, d: Wr.Dec<Da.Disk>, dp: PDx.dx.DP(s2, d)) -> dce.EP(s, FDa.get_ev.first(x, d)):
  match d:
    case Wr.Got{+f, +s3}:
      (e, g) = dp
      dce.matches(s, x, f, s3, Equal.trans(String, s, Wr.put_nat(0n, Dash.sp_w_first(x, s2)), Wr.put_nat(0n, Dash.sp_w_first(x, Dash.sp_w_disk(f, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Dash.sp_w_first(x, z)), s2, Dash.sp_w_disk(f, s3), e)), dce.and_tt(Dash.sp_fit_first(x), Dash.sp_fit_disk(f), fx, g), Wr.get_bool(s3), dce.bool(s3))
    case Wr.Bad{}:
      Unit{}

def dce.ev.pair(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Da.First>, fp: dce.FP(s1, d)) -> dce.EP(s, FDa.get_ev.pair(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e, g) = fp
      dce.ev.first(s, x, s2, PDx.dx.after(s, 0n, s1, Dash.sp_w_first(x, s2), pre, e), g, FDa.get_file(Wr.get_nat(s2)), PDx.dx.disk(s2))
    case Wr.Bad{}:
      Unit{}

def dce.later(-s: String, +f: Da.Disk, -s2: String, pre: {s == Wr.put_nat(1n, Dash.sp_w_disk(f, s2)) : String}, ff: {Dash.sp_fit_disk(f) == True{} : Bool}, d: Wr.Dec<Bool>, bp: dce.BP(s2, d)) -> dce.EP(s, FDa.get_ev.later(f, d)):
  match d:
    case Wr.Got{+m, +r}:
      (Equal.trans(String, s, Wr.put_nat(1n, Dash.sp_w_disk(f, s2)), Wr.put_nat(1n, Dash.sp_w_disk(f, Wr.put_bool(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Dash.sp_w_disk(f, z)), s2, Wr.put_bool(m, r), bp)), ff)
    case Wr.Bad{}:
      Unit{}

def dce.ev.frame(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Da.Disk>, dp: PDx.dx.DP(s1, d)) -> dce.EP(s, FDa.get_ev.frame(d)):
  match d:
    case Wr.Got{+f, +s2}:
      (e, g) = dp
      dce.later(s, f, s2, PDx.dx.after(s, 1n, s1, Dash.sp_w_disk(f, s2), pre, e), g, Wr.get_bool(s2), dce.bool(s2))
    case Wr.Bad{}:
      Unit{}

def dce.ev.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dce.EP(s, FDa.get_ev.tag(t, s1)):
  match t:
    case 0n:
      dce.ev.pair(s, s1, pre, FDa.get_first(Wr.get_nat(s1)), dce.first(s1))
    case 1n:
      dce.ev.frame(s, s1, pre, FDa.get_file(Wr.get_nat(s1)), PDx.dx.disk(s1))
    case 2n+u:
      Unit{}

def dce.ev.go(-s: String, d: Wr.Dec<Nat>, np: PDx.dx.NP(s, d)) -> dce.EP(s, FDa.get_ev.go(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dce.ev.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dce.ev(+s: String) -> dce.EP(s, FDa.get_ev(s)):
  dce.ev.go(s, Wr.get_nat(s), PDx.dx.nat(s))

# a verdict answered: an event read whole, nothing left
def dce.top(-s: String, +c: Da.Conn, d: Wr.Dec<Da.CEv>, ep: dce.EP(s, d), ok: {LawsBase.wire_opens_err(DashConn.cs_out(FDa.step.ev(c, d))) == False{} : Bool}) -> Sigma<&1, &1, Da.CEv, e => {s == DashConn.sp_w_ev(e, "") : String} & {DashConn.sp_fit_ev(e) == True{} : Bool}>:
  match d:
    case Wr.Got{+e, rest}:
      match rest:
        case SNil{}:
          (e, ep)
        case SCon{x, y}:
          LA.dcn.absurdT(Sigma<&1, &1, Da.CEv, e2 => {s == DashConn.sp_w_ev(e2, "") : String} & {DashConn.sp_fit_ev(e2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.dcn.absurdT(Sigma<&1, &1, Da.CEv, e2 => {s == DashConn.sp_w_ev(e2, "") : String} & {DashConn.sp_fit_ev(e2) == True{} : Bool}>, ok)

def DashConn.dash_conn_entry_exact(c, s, ok):
  dce.top(s, c, FDa.get_ev(s), dce.ev(s), ok)
