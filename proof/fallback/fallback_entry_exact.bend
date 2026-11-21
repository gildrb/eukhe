# eukhe: the proof of LAW fallback_entry_exact
#
# PROOF: the entry answers a value only for a list read whole with nothing
# left (fbx.top), which is the list encoding of the Nats it read
# (Wire.wire_list_exact) with its count and every Nat within the wire
# (NL.nl.nl), and only when those Nats parse; a parse is exact: the Nats
# are the request's (LA.fbb.parse_px).

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/fallback.bend as Fallback
import ../wire/wire_list_exact.bend as PWireListExact
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ../base/staging.bend as LStg
import ./base.bend as LA

def fbx.G(s: String) -> Type:
  Sigma<&1, &1, Fb.In, x => {s == Fallback.fb_req(x, "") : String} & {Fallback.fb_fits(x) == True{} : Bool}>

# the list encoding of a request's Nats is its spelling
def fbx.eq(+s: String, +xs: List<&2, Nat>, +x: Fb.In, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, v: {xs == Fallback.fb_nats(x) : List<&2, Nat>}) -> {s == Fallback.fb_req(x, "") : String}:
  %v : {s == Wr.put_list(~Nat, ~Wr.put_nat, _, "") : String}
  es

# a request whose Nats fit the wire fits
def fbx.fits(+xs: List<&2, Nat>, +x: Fb.In, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, +v: {xs == Fallback.fb_nats(x) : List<&2, Nat>}) -> {Fallback.fb_fits(x) == True{} : Bool}:
  %v : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(Fallback.fb_nats(x))) == True{} : Bool}
  %v : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  f

# a parsed request: the spelling and the fit of its Nats are its own
def fbx.done(+s: String, +xs: List<&2, Nat>, +x: Fb.In, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, +v: {xs == Fallback.fb_nats(x) : List<&2, Nat>}) -> fbx.G(s):
  (x, (fbx.eq(s, xs, x, es, v), fbx.fits(xs, x, f, v)))

def fbx.pick(+s: String, +xs: List<&2, Nat>, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, r: Maybe<&2, Fb.In>, v: LA.fbb.PX(xs, r), ok: {LawsBase.wire_opens_err(FFb.ffi.parsed(r)) == False{} : Bool}) -> fbx.G(s):
  match r:
    case None{}:
      LStg.stg.absurd(fbx.G(s), ok)
    case Some{+x}:
      fbx.done(s, xs, x, es, f, v)

def fbx.top(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {FFb.get_req(s) == d : Wr.Dec<List<&2, Nat>>}, nl: NL.nl.NL(s, d), ok: {LawsBase.wire_opens_err(FFb.ffi.got(d)) == False{} : Bool}) -> fbx.G(s):
  match d:
    case Wr.Got{+xs, rest}:
      match rest:
        case SNil{}:
          (es, f) = nl
          fbx.pick(s, xs, Wire.wire_list_exact(s, xs, "", ed), f, FFb.parse(xs), LA.fbb.parse_px(xs), ok)
        case SCon{c, y}:
          LStg.stg.absurd(fbx.G(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(fbx.G(s), ok)

def Fallback.fallback_entry_exact(s, ok):
  fbx.top(s, FFb.get_req(s), {==}, NL.nl.nl(s), ok)
