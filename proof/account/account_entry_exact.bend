# eukhe: the proof of LAW account_entry_exact
#
# PROOF: the entry answers a value only for a list read whole with nothing
# left (acx.top), which is the list encoding of the Nats it read
# (Wire.wire_list_exact) with its count and every Nat within the wire
# (NL.nl.nl), and only when those Nats parse; a parse is exact: the Nats
# are the request's (LA.acb.parse_px).

import Base
import ../../bend/account.bend as Ac
import ../../bend/ffi_account.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/account.bend as Account
import ../wire/wire_list_exact.bend as PWireListExact
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ../base/staging.bend as LStg
import ./base.bend as LA

def acx.G(s: String) -> Type:
  Sigma<&1, &1, Ac.In, x => {s == Account.ac_req(x, "") : String} & {Account.ac_fits(x) == True{} : Bool}>

# the list encoding of a request's Nats is its spelling
def acx.eq(+s: String, +xs: List<&2, Nat>, +x: Ac.In, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, v: {xs == Account.ac_nats(x) : List<&2, Nat>}) -> {s == Account.ac_req(x, "") : String}:
  %v : {s == Wr.put_list(~Nat, ~Wr.put_nat, _, "") : String}
  es

# a request whose Nats fit the wire fits
def acx.fits(+xs: List<&2, Nat>, +x: Ac.In, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, +v: {xs == Account.ac_nats(x) : List<&2, Nat>}) -> {Account.ac_fits(x) == True{} : Bool}:
  %v : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(Account.ac_nats(x))) == True{} : Bool}
  %v : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  f

# a parsed request: the spelling and the fit of its Nats are its own
def acx.done(+s: String, +xs: List<&2, Nat>, +x: Ac.In, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, +v: {xs == Account.ac_nats(x) : List<&2, Nat>}) -> acx.G(s):
  (x, (acx.eq(s, xs, x, es, v), acx.fits(xs, x, f, v)))

def acx.pick(+s: String, +xs: List<&2, Nat>, es: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}, r: Maybe<&2, Ac.In>, v: LA.acb.PX(xs, r), ok: {LawsBase.wire_opens_err(FAc.ffi.parsed(r)) == False{} : Bool}) -> acx.G(s):
  match r:
    case None{}:
      LStg.stg.absurd(acx.G(s), ok)
    case Some{+x}:
      acx.done(s, xs, x, es, f, v)

def acx.top(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {FAc.get_req(s) == d : Wr.Dec<List<&2, Nat>>}, nl: NL.nl.NL(s, d), ok: {LawsBase.wire_opens_err(FAc.ffi.got(d)) == False{} : Bool}) -> acx.G(s):
  match d:
    case Wr.Got{+xs, rest}:
      match rest:
        case SNil{}:
          (es, f) = nl
          acx.pick(s, xs, Wire.wire_list_exact(s, xs, "", ed), f, FAc.parse(xs), LA.acb.parse_px(xs), ok)
        case SCon{c, y}:
          LStg.stg.absurd(acx.G(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(acx.G(s), ok)

def Account.account_entry_exact(s, ok):
  acx.top(s, FAc.get_req(s), {==}, NL.nl.nl(s), ok)
