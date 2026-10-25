# eukhe: the proof of LAW dash_policy_entry_exact
#
# PROOF: the decoder answers Got{n, rest} only for an input that is the
# spelling of n before rest (wire_str_exact), with n's length within the
# wire (a longer count is refused: wire_nat_too_long). The entry answers
# a verdict only for a request read whole with nothing left: that input is
# the spelled request (dpx.top).

import Base
import ../../bend/ffi_dash_policy.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ../base/staging.bend as LStg

def dpx.DT(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

# a decoder answered Got and Bad
def dpx.got_bad(-A: Data, -G: Type, -x: A, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<A>}) -> G:
  %e : dpx.DT(A, _, G)
  Unit{}

# a decoded string's length fits: a longer one's count is refused
def dpx.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      dpx.got_bad(String, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def dpx.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dpx.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> dpx.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, dpx.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def dpx.top(-s: String, d: Wr.Dec<String>, sp: dpx.SP(s, d), ok: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, String, n => {s == Wr.put_str(n, "") : String} & {LawsBase.wire_fits(String.length(n)) == True{} : Bool}>:
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (a, sp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, String, n2 => {s == Wr.put_str(n2, "") : String} & {LawsBase.wire_fits(String.length(n2)) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, String, n2 => {s == Wr.put_str(n2, "") : String} & {LawsBase.wire_fits(String.length(n2)) == True{} : Bool}>, ok)

def DashPolicy.dash_policy_entry_exact(s, ok):
  dpx.top(s, FDp.get_req(s), dpx.str.at(s, Wr.get_str(s), {==}), ok)
