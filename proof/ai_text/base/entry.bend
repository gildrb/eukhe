# eukhe: lemmas of the ai_text entry proofs: a spelled request that fits
# reads back (aite.req_rt), the answer is the spelled model answer
# (aite.answer), and the decoder answers Got only for the spelling of a
# request that fits, then its rest (aite.rp_all).

import Base
import ../../../bend/ai_text.bend as T
import ../../../bend/ffi_ai_text.bend as FT
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/ai_text.bend as AiText
import ../../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../base/wire.bend as LBaseWire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../model_name/base/exact.bend as LX

# Reading back
# ------------

def aite.req_rt(q: FT.Req, +rest: String, h: {AiText.sp_fit_req(q) == True{} : Bool}) -> {FT.get_req(AiText.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FT.Req>}:
  match q:
    case FT.QMajor{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FT.get_req.major(_) == Wr.Got{FT.QMajor{x}, rest} : Wr.Dec<FT.Req>}
      {==}
    case FT.QApi{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FT.get_req.api(_) == Wr.Got{FT.QApi{x}, rest} : Wr.Dec<FT.Req>}
      {==}
    case FT.QData{+cs}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FT.get_strs(LawsBase.wire_spell_strs(cs, rest)), Wr.Got{cs, rest}, Wire.wire_strs_round_trip(cs, rest, h)) : {FT.get_req.data(_) == Wr.Got{FT.QData{cs}, rest} : Wr.Dec<FT.Req>}
      {==}
    case FT.QBound{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FT.get_req.bound(_) == Wr.Got{FT.QBound{x}, rest} : Wr.Dec<FT.Req>}
      {==}
    case FT.QLines{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FT.get_req.lines(_) == Wr.Got{FT.QLines{x}, rest} : Wr.Dec<FT.Req>}
      {==}

# The answer
# ----------

def aite.mstr(m: Maybe<&2, String>) -> {FT.put_mstr(m) == AiText.sp_w_mstr(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def aite.mnat(m: Maybe<&2, Nat>) -> {FT.put_mnat(m) == AiText.sp_w_mnat(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def aite.span(m: Maybe<&2, T.Span>) -> {FT.put_span(m) == AiText.sp_w_span(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case T.Span{i, l}:
          {==}

# the entry's answer to a request is the spelled model answer
def aite.answer(q: FT.Req) -> {FT.answer(q) == AiText.sp_w_reply(q) : String}:
  match q:
    case FT.QMajor{x}:
      aite.mstr(T.gemini_major(x))
    case FT.QApi{x}:
      {==}
    case FT.QData{cs}:
      aite.mnat(T.data_url(cs))
    case FT.QBound{x}:
      aite.span(T.event_boundary(x))
    case FT.QLines{x}:
      Wire.wire_strs_spells(T.lines(x), "")

# Exactness
# ---------

def aite.RP(s: String, d: Wr.Dec<FT.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == AiText.sp_w_req(q, r) : String} & {AiText.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def aite.x_major(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> aite.RP(s, FT.get_req.major(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 0n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def aite.x_api(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> aite.RP(s, FT.get_req.api(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 1n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def aite.x_data(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FT.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> aite.RP(s, FT.get_req.data(d)):
  match d:
    case Wr.Got{+xs, +rr}:
      +ee = ed
      (LX.mnx.app(s, 2n, s0, LawsBase.wire_spell_strs(xs, rr), pre, Wire.wire_strs_exact(s0, xs, rr, ee)), Wire.wire_strs_decoded_fit(s0, xs, rr, ee))
    case Wr.Bad{}:
      Unit{}

def aite.x_bound(-s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> aite.RP(s, FT.get_req.bound(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 3n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def aite.x_lines(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> aite.RP(s, FT.get_req.lines(d)):
  match d:
    case Wr.Got{+x, +rr}:
      +ee = ed
      (LX.mnx.app(s, 4n, s0, Wr.put_str(x, rr), pre, Wire.wire_str_exact(s0, x, rr, ee)), Wire.wire_str_decoded_fits(s0, x, rr, ee))
    case Wr.Bad{}:
      Unit{}

def aite.x_req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> aite.RP(s, FT.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          aite.x_major(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_str(s0), {==})
        case 1n:
          aite.x_api(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_str(s0), {==})
        case 2n:
          aite.x_data(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FT.get_strs(s0), {==})
        case 3n:
          aite.x_bound(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_str(s0), {==})
        case 4n:
          aite.x_lines(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_str(s0), {==})
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads from s is the spelling of what it read, then
# its rest, and fits the wire
def aite.rp_all(+s: String) -> aite.RP(s, FT.get_req(s)):
  aite.x_req(s, Wr.get_nat(s), {==})
