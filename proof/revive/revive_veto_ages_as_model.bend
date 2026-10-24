# eukhe: the proof of LAW revive_veto_ages_as_model
# A stamp at `at`, a boot at at + a: the stamp is never past the skew
# (at <= (at + a) + k) and its age is a ((at + a) - at), so the veto's
# freshness is Rv.fresh(m, a).

import Base
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive

def rva.le0(x: Nat) -> {True{} == Nat.is_le(0n, x) : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# at is at most (at + a) + k
def rva.le(at: Nat, +a: Nat, +k: Nat) -> {True{} == Nat.is_le(at, Nat.add(Nat.add(at, a), k)) : Bool}:
  match at:
    case 0n:
      rva.le0(Nat.add(a, k))
    case 1n+p:
      rva.le(p, a, k)

def rva.sub0(a: Nat) -> {a == Nat.sub(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (at + a) - at is a
def rva.sub(at: Nat, +a: Nat) -> {a == Nat.sub(Nat.add(at, a), at) : Nat}:
  match at:
    case 0n:
      rva.sub0(a)
    case 1n+p:
      rva.sub(p, a)

def Revive.revive_veto_ages_as_model(at, a, m, k):
  %rva.le(at, a, k) : {Rv.veto.fresh(Bool.and(_, Nat.is_le(Nat.sub(Nat.add(at, a), at), m))) == Rv.veto.fresh(Rv.fresh(m, a)) : Rv.Veto}
  %rva.sub(at, a) : {Rv.veto.fresh(Bool.and(True{}, Nat.is_le(_, m))) == Rv.veto.fresh(Rv.fresh(m, a)) : Rv.Veto}
  {==}
