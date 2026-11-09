# eukhe: the proof of LAW dash_keep_open_narrowed
#
# PROOF: the file's token is R2's (dash_stored_spec), there here, so the
# mode decides (pa.held_some). 64 u + r leaves what r leaves by 64: each 64
# counts one more quotient and starts the remainder again (km.shift, by
# induction on u; km.d: the count does not change the remainder). For the
# 63 values of 8 g + o with octal digits g, o not both 0 the remainder is
# not 0 (kn.low, computed per digit pair), so the file is narrowed.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_stored_spec.bend as PDashStoredSpec

# the file's token, read by the code, is there as R2 says
def kon.has(+f: Da.Disk, -x: Bool, e: {Dash.sp_has(Dash.sp_stored(f)) == x : Bool}) -> {Dash.sp_has(Da.stored(f)) == x : Bool}:
  Equal.trans(Bool, Dash.sp_has(Da.stored(f)), Dash.sp_has(Dash.sp_stored(f)), x, Equal.cong(Maybe<&2, List<&2, Nat>>, Bool, z => Dash.sp_has(z), Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)), e)

# the remainder by 64 does not see the counted quotient
def km.d(n: Nat, m: Nat, +d: Nat, +e: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, e, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          km.d(np, r, 1n+d, 1n+e, 0n)
        case 1n+mp:
          km.d(np, mp, d, e, 1n+r)

# 64 u + r leaves what r leaves
def km.shift(u: Nat, +r: Nat, +d: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(u, 64n), r), 63n, d, 0n)) == Pair.snd(Nat, Nat, Nat.divmod.go(r, 63n, 0n, 0n)) : Nat}:
  match u:
    case 0n:
      km.d(r, 63n, d, 0n, 0n)
    case 1n+p:
      km.shift(p, r, 1n+d)

# no digit is below 0
def kn.lt0(-G: Type, q: Nat, e: {Nat.is_lt(q, 0n) == True{} : Bool}) -> G:
  match q:
    case 0n:
      LA.dashboard_auth.pa.absurdF(G, e)
    case 1n+p:
      LA.dashboard_auth.pa.absurdF(G, e)

def kn.low(g: Nat, o: Nat, gd: {Nat.is_lt(g, 8n) == True{} : Bool}, od: {Nat.is_lt(o, 8n) == True{} : Bool}, open: {Nat.is_eq(Nat.add(g, o), 0n) == False{} : Bool}) -> {Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(g, 8n), o), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}:
  match g:
    case 0n:
      match o:
        case 0n:
          LA.dashboard_auth.pa.absurdT({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(0n, 8n), 0n), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, open)
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(0n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 1n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(1n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 2n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(2n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 3n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(3n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 4n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(4n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 5n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(5n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 6n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(6n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 7n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(7n, 8n), 8n+q), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, od)
    case 8n+q:
      kn.lt0({Da.keep.private(Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(8n+q, 8n), o), 63n, 0n, 0n)), 0n)) == Da.Restrict{} : Da.Keep}, q, gd)

def Dash.dash_keep_open_narrowed(s, u, g, o, holds, gd, od, open):
  +r = Nat.add(Nat.mul(g, 8n), o)
  +h2 = kon.has(Da.Holds{s}, True{}, holds)
  %Equal.sym(Da.Keep, Da.keep.held(Da.stored(Da.Holds{s}), Nat.add(Nat.mul(u, 64n), r)), Da.keep.mode(Nat.add(Nat.mul(u, 64n), r)), LA.pa.held_some(Da.stored(Da.Holds{s}), Nat.add(Nat.mul(u, 64n), r), h2)) : {_ == Da.Restrict{} : Da.Keep}
  %Equal.sym(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(u, 64n), r), 63n, 0n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(r, 63n, 0n, 0n)), km.shift(u, r, 0n)) : {Da.keep.private(Nat.is_eq(_, 0n)) == Da.Restrict{} : Da.Keep}
  kn.low(g, o, gd, od, open)
