# eukhe: the proof of LAW line_fits_exact
# A text's Text.len is its bytes (PLSE.lse.len); a positive count is one
# above 0.

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../laws/compactor.bend as Compactor
import ./line_step_exact.bend as PLSE

def lfe.pos(n: Nat) -> {Nat.is_lt(0n, n) == OBits.Nat.is_pos(n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def lfe.some(+node: Nat, +t: List<&2, C.W>) -> {C.line.fits(node, Some{t}) == Compactor.fits_spec(node, Some{t}) : Bool}:
  %Equal.sym(Nat, C.Text.len(t), Compactor.bytes(t), PLSE.lse.len(t)) : {Bool.and(OBits.Nat.is_pos(_), Nat.is_le(_, node)) == Bool.and(Nat.is_lt(0n, Compactor.bytes(t)), Nat.is_le(Compactor.bytes(t), node)) : Bool}
  %lfe.pos(Compactor.bytes(t)) : {Bool.and(_, Nat.is_le(Compactor.bytes(t), node)) == Bool.and(Nat.is_lt(0n, Compactor.bytes(t)), Nat.is_le(Compactor.bytes(t), node)) : Bool}
  {==}

def Compactor.line_fits_exact(node, m):
  match m:
    case None{}:
      {==}
    case Some{t}:
      lfe.some(node, t)
