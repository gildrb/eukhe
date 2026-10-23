# eukhe: the proof of LAW replace_rank_cut

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base.bend as L

# a text no longer than n is its first 1 + n chars
def fr.take_all(s: String, n: Nat, h: {Nat.is_le(String.length(s), n) == True{} : Bool}) -> {String.take(s, 1n+n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match n:
        case 0n:
          L.wr_absurd({String.take(SCon{c, t}, 1n) == SCon{c, t} : String}, h)
        case 1n+m:
          Equal.cong(String, String, x => SCon{c, x}, String.take(t, 1n+m), t, fr.take_all(t, m, h))

# the first 1 + n chars of a text longer than n are longer than n
def fr.take_long(s: String, n: Nat, h: {Nat.is_le(String.length(s), n) == False{} : Bool}) -> {Nat.is_le(String.length(String.take(s, 1n+n)), n) == False{} : Bool}:
  match s:
    case SNil{}:
      match n:
        case 0n:
          L.wr_absurd({Nat.is_le(0n, 0n) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
        case 1n+m:
          L.wr_absurd({Nat.is_le(0n, 1n+m) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case SCon{c, t}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          fr.take_long(t, m, h)

def fr.cut_at(b: Bool, +s: String, +eb: {Nat.is_le(String.length(s), 64n) == b : Bool}) -> {Rp.rank(String.take(s, 65n)) == Rp.rank.cap(b, s) : List<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(String, String.take(s, 65n), s, fr.take_all(s, 64n, eb)) : {Rp.rank(_) == Rp.rank.cap(True{}, s) : List<&2, Nat>}
      %Equal.sym(Bool, Nat.is_le(String.length(s), 64n), True{}, eb) : {Rp.rank.cap(_, s) == Rp.rank.cap(True{}, s) : List<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(String.length(String.take(s, 65n)), 64n), False{}, fr.take_long(s, 64n, eb)) : {Rp.rank.cap(_, String.take(s, 65n)) == Rp.rank.cap(False{}, s) : List<&2, Nat>}
      {==}

def Replace.replace_rank_cut(s):
  fr.cut_at(Nat.is_le(String.length(s), 64n), s, {==})
