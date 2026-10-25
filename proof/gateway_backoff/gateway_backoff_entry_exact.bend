# eukhe: the proof of LAW gateway_backoff_entry_exact
#
# PROOF: the decoder answers Got{m, rest} only for an input that is the
# spelling of m before rest, with the last wait within the wire
# (wire_nat_exact, wire_nat_decoded_fits); the entry answers a wait only
# for a request read whole with nothing left (gbx.top).

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/staging.bend as LStg

def gbx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gbx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> gbx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def gbx.nat(+s: String) -> gbx.NP(s, Wr.get_nat(s)):
  gbx.nat.at(s, Wr.get_nat(s), {==})

def gbx.RP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == GatewayBackoff.gb_w_req(m, r) : String} & {GatewayBackoff.gb_fit(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gbx.some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: gbx.NP(s1, d)) -> gbx.RP(s, FGb.get_req.some(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(n, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(n, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def gbx.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> gbx.RP(s, FGb.get_req.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      gbx.some(s, s1, pre, Wr.get_nat(s1), gbx.nat(s1))
    case 2n+u:
      Unit{}

def gbx.go(-s: String, d: Wr.Dec<Nat>, np: gbx.NP(s, d)) -> gbx.RP(s, FGb.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      gbx.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def gbx.top(-s: String, d: Wr.Dec<Maybe<&2, Nat>>, rp: gbx.RP(s, d), ok: {LawsBase.wire_opens_err(FGb.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Maybe<&2, Nat>, v => {s == GatewayBackoff.gb_w_req(v, "") : String} & {GatewayBackoff.gb_fit(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+m, rest}:
      match rest:
        case SNil{}:
          (m, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Maybe<&2, Nat>, v2 => {s == GatewayBackoff.gb_w_req(v2, "") : String} & {GatewayBackoff.gb_fit(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Maybe<&2, Nat>, v2 => {s == GatewayBackoff.gb_w_req(v2, "") : String} & {GatewayBackoff.gb_fit(v2) == True{} : Bool}>, ok)

def GatewayBackoff.gateway_backoff_entry_exact(s, ok):
  gbx.top(s, FGb.get_req(s), gbx.go(s, Wr.get_nat(s), gbx.nat(s)), ok)
