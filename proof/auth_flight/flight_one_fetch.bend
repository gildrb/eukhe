# eukhe: the proof of LAW flight_one_fetch

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# The laws
# --------

def pf.zero_fetching(cs: List<&2, F.Leg>, z: {LA.pf.leads(cs) == 0n : Nat}) -> {F.fetching(cs) == 0n : Nat}:
  match cs:
    case Nil{}:
      {==}
    case l <> t:
      match l:
        case F.Load{}:
          pf.zero_fetching(t, z)
        case F.Board{}:
          pf.zero_fetching(t, z)
        case F.Check{f}:
          LLogicLogic.pf.succ_ne_zero({F.fetching(t) == 0n : Nat}, LA.pf.leads(t), z)
        case F.Fetch{f}:
          LLogicLogic.pf.succ_ne_zero({1n+F.fetching(t) == 0n : Nat}, LA.pf.leads(t), z)
        case F.Store{f, c}:
          LLogicLogic.pf.succ_ne_zero({F.fetching(t) == 0n : Nat}, LA.pf.leads(t), z)
        case F.Land{f, o}:
          LLogicLogic.pf.succ_ne_zero({F.fetching(t) == 0n : Nat}, LA.pf.leads(t), z)
        case F.Waiting{f}:
          pf.zero_fetching(t, z)
        case F.Served{v, o}:
          pf.zero_fetching(t, z)

# one leader and a flight in flight: no other caller leads
def pf.one_holds(b: Bool, -x: Nat, e: {1n+x == LA.pf.holds(b) : Nat}) -> {x == 0n : Nat}:
  match b:
    case True{}:
      LA.pf.succ_inj(x, 0n, e)
    case False{}:
      LLogicLogic.pf.succ_ne_zero({x == 0n : Nat}, x, e)

def pf.le_zero_fetching(+t: List<&2, F.Leg>, +b: Bool, e: {1n+LA.pf.leads(t) == LA.pf.holds(b) : Nat}, +n: Nat) -> {F.le(F.fetching(t), n) == True{} : Bool}:
  %Equal.sym(Nat, F.fetching(t), 0n, pf.zero_fetching(t, pf.one_holds(b, LA.pf.leads(t), e))) : {F.le(_, n) == True{} : Bool}
  {==}

def pf.fetch_le(cs: List<&2, F.Leg>, +b: Bool, e: {LA.pf.leads(cs) == LA.pf.holds(b) : Nat}) -> {F.le(F.fetching(cs), 1n) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case l <> +t:
      match l:
        case F.Load{}:
          pf.fetch_le(t, b, e)
        case F.Board{}:
          pf.fetch_le(t, b, e)
        case F.Check{f}:
          pf.le_zero_fetching(t, b, e, 1n)
        case F.Fetch{f}:
          pf.le_zero_fetching(t, b, e, 0n)
        case F.Store{f, c}:
          pf.le_zero_fetching(t, b, e, 1n)
        case F.Land{f, o}:
          pf.le_zero_fetching(t, b, e, 1n)
        case F.Waiting{f}:
          pf.fetch_le(t, b, e)
        case F.Served{v, o}:
          pf.fetch_le(t, b, e)

def pf.one_fetch(s: F.St, inv: LA.auth_flight.pf.Inv(s)) -> {F.le(F.fetching(F.St.cs(s)), 1n) == True{} : Bool}:
  match s:
    case F.St{+w, +cs}:
      (cnt, all) = inv
      pf.fetch_le(cs, F.W.fl(w), cnt)

# The laws, for PROOF.bend
# ------------------------

def pf.flight_one_fetch(+evs: List<&2, F.Ev>) -> {F.le(F.fetching(F.St.cs(F.run(evs))), 1n) == True{} : Bool}:
  pf.one_fetch(F.run(evs), LA.pf.inv_run(evs))

# (A1) One refresh flight per provider

def AuthFlight.flight_one_fetch(evs):
  pf.flight_one_fetch(evs)
