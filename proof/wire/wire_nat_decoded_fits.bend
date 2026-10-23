# eukhe: the proof of LAW wire_nat_decoded_fits

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ./wire_nat_exact.bend as PWireNatExact
import ./wire_nat_too_long.bend as PWireNatTooLong

def wn_dfh(b: Bool, +s: String, +n: Nat, +rest: String, eb: {LawsBase.wire_fits(n) == b : Bool},
  +h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}) -> {LawsBase.wire_fits(n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +ex = Wire.wire_nat_exact(s, n, rest, h)
      +tl = Wire.wire_nat_too_long(n, rest, eb)
      LA.wn_bad_got({LawsBase.wire_fits(n) == True{} : Bool}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Bad{}, tl),
          Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.get_nat(s), Wr.Got{n, rest},
            Equal.cong(String, Wr.Dec<Nat>, y => Wr.get_nat(y), Wr.put_nat(n, rest), s, Equal.sym(String, s, Wr.put_nat(n, rest), ex)), h)))

def Wire.wire_nat_decoded_fits(s, n, rest, h):
  wn_dfh(LawsBase.wire_fits(n), s, n, rest, {==}, h)
