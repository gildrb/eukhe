# eukhe: the proof of LAW tui_usage_band_exact
# An unknown window reaches no share; a known one reaches each share
# exactly when the spec counts it (the three tests are the same terms,
# counted by TC.one and by the spec's bit).

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def ube.count(+a: Bool, +b: Bool, +c: Bool) -> {Nat.add(TC.one(a), Nat.add(TC.one(b), Nat.add(TC.one(c), 0n))) == Nat.add(TuiColor.bit(a), Nat.add(TuiColor.bit(b), TuiColor.bit(c))) : Nat}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def TuiColor.tui_usage_band_exact(t, w):
  match w:
    case 0n:
      {==}
    case 1n+v:
      +x = {1n+v : Nat}
      ube.count(Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n)), Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n)), Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)))
