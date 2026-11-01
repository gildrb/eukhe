# eukhe: lemmas the proofs of area headless_settle share: a pending run
# never stops; the entry's decoder is the laws' reader
# (spec/durable/headless_wire.bend), stage by stage; a spelled request
# that fits reads back whole

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/ffi_headless_settle.bend as FHs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_settle.bend as HeadlessSettle
import ../../spec/durable/headless_wire.bend as SpW
import ../base/logic/bool.bend as LLogicBool
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../base/wire.bend as LWire

# a run with pending work never stops, at the limit or not
def hs.stays(l: Bool) -> {HeadlessSettle.finished(Hs.decide(True{}, l)) == False{} : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}

# The reader
# ----------

def hs.limit(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, u: Bool, d: Wr.Dec<Bool>) -> {FHs.get_facts.limit(b, j, k, c, w, x, u, d) == SpW.r_settle.limit(b, j, k, c, w, x, u, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def hs.unknown(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, d: Wr.Dec<Bool>) -> {FHs.get_facts.unknown(b, j, k, c, w, x, d) == SpW.r_settle.unknown(b, j, k, c, w, x, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{u, s}:
      hs.limit(b, j, k, c, w, x, u, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hs.wakes(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, d: Wr.Dec<Nat>) -> {FHs.get_facts.wakes(b, j, k, c, w, d) == SpW.r_settle.wakes(b, j, k, c, w, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{x, s}:
      hs.unknown(b, j, k, c, w, x, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hs.runs(b: Bool, j: Nat, k: Nat, c: Nat, d: Wr.Dec<Nat>) -> {FHs.get_facts.runs(b, j, k, c, d) == SpW.r_settle.runs(b, j, k, c, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{w, s}:
      hs.wakes(b, j, k, c, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def hs.children(b: Bool, j: Nat, k: Nat, d: Wr.Dec<Nat>) -> {FHs.get_facts.children(b, j, k, d) == SpW.r_settle.children(b, j, k, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{c, s}:
      hs.runs(b, j, k, c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def hs.kernel(b: Bool, j: Nat, d: Wr.Dec<Nat>) -> {FHs.get_facts.kernel(b, j, d) == SpW.r_settle.kernel(b, j, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{k, s}:
      hs.children(b, j, k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def hs.jobs(b: Bool, d: Wr.Dec<Nat>) -> {FHs.get_facts.jobs(b, d) == SpW.r_settle.jobs(b, d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{j, s}:
      hs.kernel(b, j, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def hs.busy(d: Wr.Dec<Bool>) -> {FHs.get_facts.busy(d) == SpW.r_settle.busy(d) : Wr.Dec<Hs.Facts>}:
  match d:
    case Wr.Got{b, s}:
      hs.jobs(b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry reads a request as the laws' reader does
def hs.req(+s: String) -> {FHs.get_facts(s) == SpW.r_settle(s) : Wr.Dec<Hs.Facts>}:
  hs.busy(Wr.get_bool(s))

# Read back
# ---------

# a spelled request that fits reads back (with the laws' reader), and the
# rest is untouched
def hs.req_rt(+f: Hs.Facts, +rest: String, +h: {SpW.fit_settle(f) == True{} : Bool}) -> {SpW.r_settle(SpW.w_settle_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Hs.Facts>}:
  match f:
    case Hs.Facts{+b, +j, +k, +c, +w, +x, +u, +l}:
      +r8 = Wr.put_bool(l, rest)
      +r7 = Wr.put_bool(u, r8)
      +r6 = Wr.put_nat(x, r7)
      +r5 = Wr.put_nat(w, r6)
      +r4 = Wr.put_nat(c, r5)
      +r3 = Wr.put_nat(k, r4)
      +r2 = Wr.put_nat(j, r3)
      -g = {Wr.Got{Hs.Facts{b, j, k, c, w, x, u, l}, rest} : Wr.Dec<Hs.Facts>}
      +hk = LLogicBool.wr_and_r(LawsBase.wire_fits(j), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)))), h)
      +hc = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x))), hk)
      +hw = LLogicBool.wr_and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)), hc)
      +hx = LLogicBool.wr_and_r(LawsBase.wire_fits(w), LawsBase.wire_fits(x), hw)
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, r2)), Wr.Got{b, r2}, Wire.wire_bool_round_trip(b, r2)) : {SpW.r_settle.busy(_) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r2), Wr.Got{j, r3}, Wire.wire_nat_round_trip(j, r3, LLogicBool.wr_and_l(LawsBase.wire_fits(j), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)))), h))) : {SpW.r_settle.jobs(b, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r3), Wr.Got{k, r4}, Wire.wire_nat_round_trip(k, r4, LLogicBool.wr_and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x))), hk))) : {SpW.r_settle.kernel(b, j, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r4), Wr.Got{c, r5}, Wire.wire_nat_round_trip(c, r5, LLogicBool.wr_and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)), hc))) : {SpW.r_settle.children(b, j, k, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r5), Wr.Got{w, r6}, Wire.wire_nat_round_trip(w, r6, LLogicBool.wr_and_l(LawsBase.wire_fits(w), LawsBase.wire_fits(x), hw))) : {SpW.r_settle.runs(b, j, k, c, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r6), Wr.Got{x, r7}, Wire.wire_nat_round_trip(x, r7, hx)) : {SpW.r_settle.wakes(b, j, k, c, w, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r7), Wr.Got{u, r8}, Wire.wire_bool_round_trip(u, r8)) : {SpW.r_settle.unknown(b, j, k, c, w, x, _) == g : Wr.Dec<Hs.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r8), Wr.Got{l, rest}, Wire.wire_bool_round_trip(l, rest)) : {SpW.r_settle.limit(b, j, k, c, w, x, u, _) == g : Wr.Dec<Hs.Facts>}
      {==}
