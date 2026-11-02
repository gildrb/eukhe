# eukhe: lemmas of the aws_text entry proofs: a spelled request that fits
# reads back (awe.req_rt), the answer is the spelled model answer
# (awe.answer), and the decoder answers Got only for the spelling of a
# request that fits, then its rest (awe.rp_all).

import Base
import ../../../bend/aws_text.bend as A
import ../../../bend/ffi_aws_text.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/aws_text.bend as AwsText
import ../../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../base/wire.bend as LBaseWire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../model_name/base/exact.bend as LX

# Reading back
# ------------

def awe.req_rt(q: FA.Req, +rest: String, h: {AwsText.sp_fit_req(q) == True{} : Bool}) -> {FA.get_req(AwsText.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FA.Req>}:
  match q:
    case FA.QPart{+r}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(r, rest)), Wr.Got{r, rest}, Wire.wire_str_round_trip(r, rest, h)) : {FA.get_req.part(_) == Wr.Got{FA.QPart{r}, rest} : Wr.Dec<FA.Req>}
      {==}
    case FA.QRid{+ns}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FA.get_strs(LawsBase.wire_spell_strs(ns, rest)), Wr.Got{ns, rest}, Wire.wire_strs_round_trip(ns, rest, h)) : {FA.get_req.rid(_) == Wr.Got{FA.QRid{ns}, rest} : Wr.Dec<FA.Req>}
      {==}
    case FA.QB64{+cs}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FA.get_strs(LawsBase.wire_spell_strs(cs, rest)), Wr.Got{cs, rest}, Wire.wire_strs_round_trip(cs, rest, h)) : {FA.get_req.b64(_) == Wr.Got{FA.QB64{cs}, rest} : Wr.Dec<FA.Req>}
      {==}
    case FA.QHost{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FA.get_req.host(_) == Wr.Got{FA.QHost{x}, rest} : Wr.Dec<FA.Req>}
      {==}
    case FA.QArn{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FA.get_req.arn(_) == Wr.Got{FA.QArn{x}, rest} : Wr.Dec<FA.Req>}
      {==}
    case FA.QFips{+r}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(r, rest)), Wr.Got{r, rest}, Wire.wire_str_round_trip(r, rest, h)) : {FA.get_req.fips(_) == Wr.Got{FA.QFips{r}, rest} : Wr.Dec<FA.Req>}
      {==}

# The answer
# ----------

def awe.mnat(m: Maybe<&2, Nat>) -> {FA.put_mnat(m) == AwsText.sp_w_mnat(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def awe.mstr(m: Maybe<&2, String>) -> {FA.put_mstr(m) == AwsText.sp_w_mstr(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the entry's answer to a request is the spelled model answer
def awe.answer(q: FA.Req) -> {FA.answer(q) == AwsText.sp_w_reply(q) : String}:
  match q:
    case FA.QPart{r}:
      awe.mnat(A.partition(r))
    case FA.QRid{ns}:
      awe.mnat(A.request_id(ns))
    case FA.QB64{cs}:
      {==}
    case FA.QHost{x}:
      awe.mstr(A.endpoint(x))
    case FA.QArn{x}:
      awe.mstr(A.arn(x))
    case FA.QFips{r}:
      {==}

# Exactness
# ---------

def awe.RP(s: String, d: Wr.Dec<FA.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == AwsText.sp_w_req(q, r) : String} & {AwsText.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def awe.x_part(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> awe.RP(s, FA.get_req.part(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 0n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_rid(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FA.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> awe.RP(s, FA.get_req.rid(d)):
  match d:
    case Wr.Got{+xs, +rr}:
      +ee = ed
      (LX.mnx.app(s, 1n, s0, LawsBase.wire_spell_strs(xs, rr), pre, Wire.wire_strs_exact(s0, xs, rr, ee)), Wire.wire_strs_decoded_fit(s0, xs, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_b64(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FA.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> awe.RP(s, FA.get_req.b64(d)):
  match d:
    case Wr.Got{+xs, +rr}:
      +ee = ed
      (LX.mnx.app(s, 2n, s0, LawsBase.wire_spell_strs(xs, rr), pre, Wire.wire_strs_exact(s0, xs, rr, ee)), Wire.wire_strs_decoded_fit(s0, xs, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_host(-s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> awe.RP(s, FA.get_req.host(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 3n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_arn(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> awe.RP(s, FA.get_req.arn(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 4n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_fips(-s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> awe.RP(s, FA.get_req.fips(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 5n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def awe.x_req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> awe.RP(s, FA.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          awe.x_part(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_str(s0), {==})
        case 1n:
          awe.x_rid(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FA.get_strs(s0), {==})
        case 2n:
          awe.x_b64(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FA.get_strs(s0), {==})
        case 3n:
          awe.x_host(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_str(s0), {==})
        case 4n:
          awe.x_arn(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_str(s0), {==})
        case 5n:
          awe.x_fips(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), Wr.get_str(s0), {==})
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads from s is the spelling of what it read, then
# its rest, and fits the wire
def awe.rp_all(+s: String) -> awe.RP(s, FA.get_req(s)):
  awe.x_req(s, Wr.get_nat(s), {==})
