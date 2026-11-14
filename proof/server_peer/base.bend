# eukhe: lemmas the proofs of area server_peer share: verdicts that
# differ, Nat.is_eq as equality, the parts of a conjunction, and a decoded
# Nat that is spelled and fits

import Base
import ../../bend/server_peer.bend as Sp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/staging.bend as LStg

# Verdicts
# --------

def spb.SD(v: Sp.Served, A: Type) -> Type:
  match v:
    case Sp.Served{}:
      A
    case Sp.OtherUid{}:
      Unit
    case Sp.NoRecord{}:
      Unit
    case Sp.OtherPid{}:
      Unit

def spb.uid_served(-A: Type, e: {Sp.OtherUid{} == Sp.Served{} : Sp.Served}) -> A:
  %e : spb.SD(_, A)
  Unit{}

def spb.none_served(-A: Type, e: {Sp.NoRecord{} == Sp.Served{} : Sp.Served}) -> A:
  %e : spb.SD(_, A)
  Unit{}

def spb.pid_served(-A: Type, e: {Sp.OtherPid{} == Sp.Served{} : Sp.Served}) -> A:
  %e : spb.SD(_, A)
  Unit{}

# Numbers
# -------

def spb.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LStg.stg.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LStg.stg.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, spb.eq_true(p, q, h))

def spb.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      spb.eq_refl(p)

# Conjunctions
# ------------

def spb.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def spb.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, e)

def spb.and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LStg.stg.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# Decoded Nats
# ------------

# what a decode of s tells: a Nat n spelled before r, n within the wire
def spb.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def spb.nat.at(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> spb.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

# a Nat decoded is spelled and fits
def spb.nat(+s: String) -> spb.NP(s, Wr.get_nat(s)):
  spb.nat.at(s, Wr.get_nat(s), {==})
