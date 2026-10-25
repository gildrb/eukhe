# eukhe: the proof of LAW gateway_answer_entry_exact
#
# PROOF: each decoder of bend/ffi_gateway_answer.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (gax.*: a predicate per decoder answer, carried stage by
# stage with wire_bool_exact and the Nat, string and list exactness lemmas
# of the doc_commit entry: dcw.nat, dcw.str, dcw.strs.list). The entry
# answers a value only for a request read whole with nothing left: that
# input is the spelled request (gax.top).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/wire.bend as Wire
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../base/wire_strs.bend as LS
import ./base.bend as LA

# Bools
# -----

def gax.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def gax.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> gax.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def gax.bool(+s: String) -> gax.BP(s, Wr.get_bool(s)):
  gax.bool.at(s, Wr.get_bool(s), {==})

# Errors (Maybe<String>)
# ----------------------

def gax.MP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == GatewayAnswer.ga_w_maybe(m, r) : String} & {GatewayAnswer.ga_fit_maybe(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gax.maybe.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> gax.MP(s, FGa.get_some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(x, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(x, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def gax.maybe.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> gax.MP(s, FGa.get_maybe.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      gax.maybe.some(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 2n+u:
      Unit{}

def gax.maybe.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gax.MP(s, FGa.get_maybe(d)):
  match d:
    case Wr.Got{t, s1}:
      gax.maybe.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def gax.maybe(+s: String) -> gax.MP(s, FGa.get_maybe(Wr.get_nat(s))):
  gax.maybe.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# Stops
# -----

def gax.StP(s: String, d: Wr.Dec<Ga.Stop>) -> Type:
  match d:
    case Wr.Got{st, r}:
      {s == Wr.put_nat(GatewayAnswer.ga_w_stop(st), r) : String}
    case Wr.Bad{}:
      Unit

def gax.stop.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> gax.StP(s, FGa.get_stop.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n:
      pre
    case 4n:
      pre
    case 5n+u:
      Unit{}

def gax.stop.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gax.StP(s, FGa.get_stop(d)):
  match d:
    case Wr.Got{t, s1}:
      gax.stop.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def gax.stop(+s: String) -> gax.StP(s, FGa.get_stop(Wr.get_nat(s))):
  gax.stop.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# The request
# -----------

def gax.RP(s: String, d: Wr.Dec<Ga.Ev>) -> Type:
  match d:
    case Wr.Got{ev, r}:
      {s == GatewayAnswer.ga_w_req(ev, r) : String} & {GatewayAnswer.ga_fit(ev) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gax.agent(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, bp: gax.BP(s1, d)) -> gax.RP(s, FGa.get_agent(d)):
  match d:
    case Wr.Got{+a, +r}:
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_bool(a, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_bool(a, r), bp)), {==})
    case Wr.Bad{}:
      Unit{}

def gax.turn.error(-s: String, +a: Bool, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_bool(a, s2)) : String}, d: Wr.Dec<Maybe<&2, String>>, mp: gax.MP(s2, d)) -> gax.RP(s, FGa.get_turn.error(a, d)):
  match d:
    case Wr.Got{+e, +r}:
      (ee, f) = mp
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_bool(a, s2)), Wr.put_nat(2n, Wr.put_bool(a, GatewayAnswer.ga_w_maybe(e, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_bool(a, z)), s2, GatewayAnswer.ga_w_maybe(e, r), ee)), f)
    case Wr.Bad{}:
      Unit{}

def gax.turn(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Bool>, bp: gax.BP(s1, d)) -> gax.RP(s, FGa.get_turn(d)):
  match d:
    case Wr.Got{+a, +s2}:
      gax.turn.error(s, a, s2, Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_bool(a, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_bool(a, s2), bp)), FGa.get_maybe(Wr.get_nat(s2)), gax.maybe(s2))
    case Wr.Bad{}:
      Unit{}

def gax.asst.error(-s: String, +st: Ga.Stop, +ts: List<&2, String>, -s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), Wr.put_list(~String, ~Wr.put_str, ts, s3))) : String}, fn: {LawsBase.wire_fits(List.length(&2, String, ts)) == True{} : Bool}, fs: {GatewayAnswer.ga_fit_strs(ts) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: gax.MP(s3, d)) -> gax.RP(s, FGa.get_assistant.error(st, ts, d)):
  match d:
    case Wr.Got{+e, +r}:
      (ee, fe) = mp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), Wr.put_list(~String, ~Wr.put_str, ts, s3))), Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), Wr.put_list(~String, ~Wr.put_str, ts, GatewayAnswer.ga_w_maybe(e, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), Wr.put_list(~String, ~Wr.put_str, ts, z))), s3, GatewayAnswer.ga_w_maybe(e, r), ee)),
        LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, ts)), Bool.and(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e)), fn, LBool.cb_and_intro(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e), fs, fe)))
    case Wr.Bad{}:
      Unit{}

def gax.asst.texts(-s: String, +st: Ga.Stop, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), s2)) : String}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, d)) -> gax.RP(s, FGa.get_assistant.texts(st, d)):
  match d:
    case Wr.Got{+ts, +s3}:
      (e, f2) = ls
      (fn, fd) = f2
      +fs = Equal.trans(Bool, GatewayAnswer.ga_fit_strs(ts), DocCommit.sp_fit_strs(ts), True{}, LA.gab.fits(ts), fd)
      gax.asst.error(s, st, ts, s3, Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), s2)), Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), Wr.put_list(~String, ~Wr.put_str, ts, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), z)), s2, Wr.put_list(~String, ~Wr.put_str, ts, s3), e)), fn, fs, FGa.get_maybe(Wr.get_nat(s3)), gax.maybe(s3))
    case Wr.Bad{}:
      Unit{}

def gax.asst(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Ga.Stop>, sp: gax.StP(s1, d)) -> gax.RP(s, FGa.get_assistant(d)):
  match d:
    case Wr.Got{+st, +s2}:
      gax.asst.texts(s, st, s2, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(GatewayAnswer.ga_w_stop(st), s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(GatewayAnswer.ga_w_stop(st), s2), sp)), Wr.get_list(~String, ~Wr.get_str, s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

def gax.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> gax.RP(s, FGa.get_req.tag(t, s1)):
  match t:
    case 0n:
      gax.agent(s, s1, pre, Wr.get_bool(s1), gax.bool(s1))
    case 1n:
      gax.asst(s, s1, pre, FGa.get_stop(Wr.get_nat(s1)), gax.stop(s1))
    case 2n:
      gax.turn(s, s1, pre, Wr.get_bool(s1), gax.bool(s1))
    case 3n:
      (pre, {==})
    case 4n+u:
      Unit{}

def gax.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gax.RP(s, FGa.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      gax.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def gax.top(-s: String, d: Wr.Dec<Ga.Ev>, rp: gax.RP(s, d), ok: {LawsBase.wire_opens_err(FGa.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Ga.Ev, v => {s == GatewayAnswer.ga_w_req(v, "") : String} & {GatewayAnswer.ga_fit(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+ev, rest}:
      match rest:
        case SNil{}:
          (ev, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Ga.Ev, v2 => {s == GatewayAnswer.ga_w_req(v2, "") : String} & {GatewayAnswer.ga_fit(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Ga.Ev, v2 => {s == GatewayAnswer.ga_w_req(v2, "") : String} & {GatewayAnswer.ga_fit(v2) == True{} : Bool}>, ok)

def GatewayAnswer.gateway_answer_entry_exact(s, ok):
  gax.top(s, FGa.get_req(s), gax.go(s, Wr.get_nat(s), LE.dcw.nat(s)), ok)
