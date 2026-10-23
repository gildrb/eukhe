# eukhe: lemmas the proofs of two or more areas share: maybe

import Base
import ../../bend/retry.bend as R
import ../../laws/base.bend as LawsBase
import ./bool/misc.bend as LBoolMisc

def themes.pt.none_some(-A: Type, -B: Data, -b: B, e: {None{} == Some{b} : Maybe<&2, B>}) -> A:
  %e : LBoolMisc.themes.pt.BD(Maybe.is_some(&2, B, _), A, Unit)
  Unit{}

def rk.keepm(ok: Bool, x: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{x}
    case False{}:
      None{}

# a number semver.bend reads, kept when it has at most 14 digits
def rk.guard(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      rk.keepm(LawsBase.rank_spec.short(x), x)

# the five checks of a switch together
def rp.Good(m: Maybe<&2, R.Switch>, len: Nat, ts: List<&2, R.Tried>, p: R.Policy) -> Type:
  {R.Switch.not_last(m, ts) == True{} : Bool} & ({R.Switch.fresh_first(m, len, ts) == True{} : Bool} & ({R.Switch.return_waits(m, ts) == True{} : Bool} & ({R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool} & {R.Switch.within(m, ts, p) == True{} : Bool})))

def rp.good_none(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(None{}, len, ts, p):
  ({==}, ({==}, ({==}, ({==}, {==}))))
