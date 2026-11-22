# eukhe: the proof of LAW restart_turn_entry_exact
#
# PROOF: the decoder answers Got{f, rest} only for an input that is the
# spelling of f before rest, with the count made within the wire
# (wire_nat_exact, wire_nat_decoded_fits); the entry answers only for a
# request read whole with nothing left (rtx.top).

import Base
import ../../bend/restart_turn.bend as Rt
import ../../bend/ffi_restart_turn.bend as FRt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/restart_turn.bend as RestartTurn
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/staging.bend as LStg

def rtx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rtx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rtx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def rtx.nat(+s: String) -> rtx.NP(s, Wr.get_nat(s)):
  rtx.nat.at(s, Wr.get_nat(s), {==})

def rtx.RP(s: String, d: Wr.Dec<Rt.Fact>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == RestartTurn.rt_w_req(f, r) : String} & {RestartTurn.rt_fit(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rtx.reopened(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, np: rtx.NP(s1, d)) -> rtx.RP(s, FRt.get_req.reopened(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(n, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def rtx.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rtx.RP(s, FRt.get_req.tag(t, s1)):
  match t:
    case 0n:
      rtx.reopened(s, s1, pre, Wr.get_nat(s1), rtx.nat(s1))
    case 1n:
      (pre, {==})
    case 2n:
      (pre, {==})
    case 3n:
      (pre, {==})
    case 4n+u:
      Unit{}

def rtx.go(-s: String, d: Wr.Dec<Nat>, np: rtx.NP(s, d)) -> rtx.RP(s, FRt.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      rtx.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def rtx.top(-s: String, d: Wr.Dec<Rt.Fact>, rp: rtx.RP(s, d), ok: {LawsBase.wire_opens_err(FRt.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Rt.Fact, v => {s == RestartTurn.rt_w_req(v, "") : String} & {RestartTurn.rt_fit(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Rt.Fact, v2 => {s == RestartTurn.rt_w_req(v2, "") : String} & {RestartTurn.rt_fit(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Rt.Fact, v2 => {s == RestartTurn.rt_w_req(v2, "") : String} & {RestartTurn.rt_fit(v2) == True{} : Bool}>, ok)

def RestartTurn.restart_turn_entry_exact(s, ok):
  rtx.top(s, FRt.get_req(s), rtx.go(s, Wr.get_nat(s), rtx.nat(s)), ok)
