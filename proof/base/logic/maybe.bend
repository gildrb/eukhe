# eukhe: lemmas the proofs of two or more areas share: logic/maybe

import Base
import ../../../laws/base.bend as LawsBase

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
