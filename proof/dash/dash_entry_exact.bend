# eukhe: the proof of LAW dash_entry_exact
#
# PROOF: each decoder of bend/ffi_dash.bend answers Got{x, rest} only for
# an input that is the spec's spelling of x before rest, with x within
# the wire (dx.*: a predicate per decoder answer, carried stage by stage
# with the wire's exactness laws wire_nat_exact and wire_str_exact, the fit
# of a decoded Nat wire_nat_decoded_fits, and the refusal of a too long
# count wire_nat_too_long). The entry answers a value only for a request
# read whole with nothing left: that input is the spelled request (dx.top).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ./base.bend as LA

# Logic
# -----

def dx.DT(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

# a decoder answered Got and Bad
def dx.got_bad(-A: Data, -G: Type, -x: A, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<A>}) -> G:
  %e : dx.DT(A, _, G)
  Unit{}

# s is the tag t then s1, and s1 is x: s is the tag t then x
def dx.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# Primitives
# ----------

def dx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def dx.nat(+s: String) -> dx.NP(s, Wr.get_nat(s)):
  dx.nat.at(s, Wr.get_nat(s), {==})

# a decoded string's length fits: a longer one's count is refused
def dx.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      dx.got_bad(String, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def dx.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dx.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> dx.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, dx.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

def dx.str(+s: String) -> dx.SP(s, Wr.get_str(s)):
  dx.str.at(s, Wr.get_str(s), {==})

# Files
# -----

def dx.DP(s: String, d: Wr.Dec<Da.Disk>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Dash.sp_w_disk(f, r) : String} & {Dash.sp_fit_disk(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dx.disk.text(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: dx.SP(s1, d)) -> dx.DP(s, FDa.get_file.text(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (dx.after(s, 2n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dx.disk.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dx.DP(s, FDa.get_file.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      dx.disk.text(s, s1, pre, Wr.get_str(s1), dx.str(s1))
    case 3n:
      (pre, {==})
    case 4n+u:
      Unit{}

def dx.disk.go(-s: String, d: Wr.Dec<Nat>, np: dx.NP(s, d)) -> dx.DP(s, FDa.get_file(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dx.disk.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dx.disk(+s: String) -> dx.DP(s, FDa.get_file(Wr.get_nat(s))):
  dx.disk.go(s, Wr.get_nat(s), dx.nat(s))

# Presented texts
# ---------------

def dx.SdP(s: String, d: Wr.Dec<Da.Said>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Dash.sp_w_said(x, r) : String} & {Dash.sp_fit_said(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dx.said.spoken(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: dx.SP(s1, d)) -> dx.SdP(s, FDa.get_said.spoken(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (dx.after(s, 0n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dx.said.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dx.SdP(s, FDa.get_said.tag(t, s1)):
  match t:
    case 0n:
      dx.said.spoken(s, s1, pre, Wr.get_str(s1), dx.str(s1))
    case 1n:
      (pre, {==})
    case 2n+u:
      Unit{}

def dx.said.go(-s: String, d: Wr.Dec<Nat>, np: dx.NP(s, d)) -> dx.SdP(s, FDa.get_said(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dx.said.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dx.said(+s: String) -> dx.SdP(s, FDa.get_said(Wr.get_nat(s))):
  dx.said.go(s, Wr.get_nat(s), dx.nat(s))

# Rotations
# ---------

def dx.RoP(s: String, d: Wr.Dec<Da.Rotation>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == Wr.put_nat(Dash.sp_w_rotation(o), r) : String}
    case Wr.Bad{}:
      Unit

def dx.rotation.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dx.RoP(s, FDa.get_rotation.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n+u:
      Unit{}

def dx.rotation.go(-s: String, d: Wr.Dec<Nat>, np: dx.NP(s, d)) -> dx.RoP(s, FDa.get_rotation(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dx.rotation.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dx.rotation(+s: String) -> dx.RoP(s, FDa.get_rotation(Wr.get_nat(s))):
  dx.rotation.go(s, Wr.get_nat(s), dx.nat(s))

# The request
# -----------

def dx.RP(s: String, d: Wr.Dec<FDa.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Dash.sp_w_req(q, r) : String} & {Dash.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dx.token(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Da.Said>, sp: dx.SdP(s1, d)) -> dx.RP(s, FDa.get_token(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (dx.after(s, 0n, s1, Dash.sp_w_said(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dx.stored(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Da.Disk>, dp: dx.DP(s1, d)) -> dx.RP(s, FDa.get_stored(d)):
  match d:
    case Wr.Got{+f, +r}:
      (e, g) = dp
      (dx.after(s, 1n, s1, Dash.sp_w_disk(f, r), pre, e), g)
    case Wr.Bad{}:
      Unit{}

def dx.keep.mode(-s: String, +o: Da.Rotation, +f: Da.Disk, -s3: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), Dash.sp_w_disk(f, s3))) : String}, ff: {Dash.sp_fit_disk(f) == True{} : Bool}, d: Wr.Dec<Nat>, np: dx.NP(s3, d)) -> dx.RP(s, FDa.get_keep.mode(o, f, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, g) = np
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), Dash.sp_w_disk(f, s3))), Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), Dash.sp_w_disk(f, Wr.put_nat(m, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), Dash.sp_w_disk(f, z))), s3, Wr.put_nat(m, r), e)), LA.pe.and_tt(Dash.sp_fit_disk(f), LawsBase.wire_fits(m), ff, g))
    case Wr.Bad{}:
      Unit{}

def dx.keep.file(-s: String, +o: Da.Rotation, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), s2)) : String}, d: Wr.Dec<Da.Disk>, dp: dx.DP(s2, d)) -> dx.RP(s, FDa.get_keep.file(o, d)):
  match d:
    case Wr.Got{+f, +s3}:
      (e, g) = dp
      dx.keep.mode(s, o, f, s3, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), s2)), Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), Dash.sp_w_disk(f, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Dash.sp_w_rotation(o), z)), s2, Dash.sp_w_disk(f, s3), e)), g, Wr.get_nat(s3), dx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def dx.keep(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Da.Rotation>, rp: dx.RoP(s1, d)) -> dx.RP(s, FDa.get_keep(d)):
  match d:
    case Wr.Got{+o, +s2}:
      dx.keep.file(s, o, s2, dx.after(s, 2n, s1, Wr.put_nat(Dash.sp_w_rotation(o), s2), pre, rp), FDa.get_file(Wr.get_nat(s2)), dx.disk(s2))
    case Wr.Bad{}:
      Unit{}

def dx.req.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dx.RP(s, FDa.get_req.tag(t, s1)):
  match t:
    case 0n:
      dx.token(s, s1, pre, FDa.get_said(Wr.get_nat(s1)), dx.said(s1))
    case 1n:
      dx.stored(s, s1, pre, FDa.get_file(Wr.get_nat(s1)), dx.disk(s1))
    case 2n:
      dx.keep(s, s1, pre, FDa.get_rotation(Wr.get_nat(s1)), dx.rotation(s1))
    case 3n+u:
      Unit{}

def dx.req.go(-s: String, d: Wr.Dec<Nat>, np: dx.NP(s, d)) -> dx.RP(s, FDa.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      dx.req.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def dx.req(+s: String) -> dx.RP(s, FDa.get_req(s)):
  dx.req.go(s, Wr.get_nat(s), dx.nat(s))

# a value answered: a request read whole, nothing left
def dx.top(-s: String, d: Wr.Dec<FDa.Req>, rp: dx.RP(s, d), ok: {LawsBase.wire_opens_err(FDa.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FDa.Req, r => {s == Dash.sp_w_req(r, "") : String} & {Dash.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LA.dashboard_auth.pa.absurdT(Sigma<&1, &1, FDa.Req, r2 => {s == Dash.sp_w_req(r2, "") : String} & {Dash.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.dashboard_auth.pa.absurdT(Sigma<&1, &1, FDa.Req, r2 => {s == Dash.sp_w_req(r2, "") : String} & {Dash.sp_fit_req(r2) == True{} : Bool}>, ok)

def Dash.dash_entry_exact(s, ok):
  dx.top(s, FDa.get_req(s), dx.req(s), ok)
