# eukhe: the proof of LAW line_fits
# Induction on the tries. A fitting reply is not empty, so it has 1 to
# node bytes; every other end is the best reply (never empty) or the
# input cut to at least 4 bytes, which keeps its first character.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/nat.bend as LNat
import ./base.bend as LA

# a cut fits its room
def pc.cut_le(t: List<&2, C.W>, room: Nat) -> {Nat.is_le(Compactor.bytes(C.cut(t, room)), room) == True{} : Bool}:
  match t:
    case Nil{}:
      LNat.compactor.pc.le_zero(room)
    case c <> rest:
      match c room:
        case C.W1{} 0n:
          {==}
        case C.W1{} 1n+r:
          pc.cut_le(rest, r)
        case C.W2{} 0n:
          {==}
        case C.W2{} 1n:
          {==}
        case C.W2{} 2n+r:
          pc.cut_le(rest, r)
        case C.W3{} 0n:
          {==}
        case C.W3{} 1n:
          {==}
        case C.W3{} 2n:
          {==}
        case C.W3{} 3n+r:
          pc.cut_le(rest, r)
        case C.W4{} 0n:
          {==}
        case C.W4{} 1n:
          {==}
        case C.W4{} 2n:
          {==}
        case C.W4{} 3n:
          {==}
        case C.W4{} 4n+r:
          pc.cut_le(rest, r)

# a text that is not empty, cut to at least 4 bytes, keeps its first
# character: 1 to 4+k bytes
def pc.cut_fits(c: C.W, t: List<&2, C.W>, k: Nat) -> {Compactor.within(4n+k, Some{C.cut(c <> t, 4n+k)}) == True{} : Bool}:
  match c:
    case C.W1{}:
      pc.cut_le(t, 3n+k)
    case C.W2{}:
      pc.cut_le(t, 2n+k)
    case C.W3{}:
      pc.cut_le(t, 1n+k)
    case C.W4{}:
      pc.cut_le(t, k)

# the best reply so far is never empty
def pc.NE(m: Maybe<&2, List<&2, C.W>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      match t:
        case Nil{}:
          Empty
        case h <> r:
          Unit

def pc.end_fits(best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, k: Nat) -> {Compactor.within(4n+k, Some{C.line.end(4n+k, best, c <> rest)}) == True{} : Bool}:
  match best:
    case None{}:
      pc.cut_fits(c, rest, k)
    case Some{b}:
      match b:
        case Nil{}:
          match nb:
        case x <> y:
          pc.cut_fits(x, y, k)

def pc.pos_len(w: C.W, -t: List<&2, C.W>) -> {Nat.is_lt(0n, Compactor.bytes(w <> t)) == True{} : Bool}:
  match w:
    case C.W1{}:
      {==}
    case C.W2{}:
      {==}
    case C.W3{}:
      {==}
    case C.W4{}:
      {==}

def pc.fits_next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +k: Nat, best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, rec: C.Line, efit: {Nat.is_le(C.Text.len(w <> t), 4n+k) == fit : Bool}, ih: {Compactor.within(4n+k, C.Line.line(rec)) == True{} : Bool}) -> {Compactor.within(4n+k, C.Line.line(C.line.next(fit, less, w <> t, 4n+k, best, c <> rest, rec))) == True{} : Bool}:
  match fit less:
    case True{} l:
      +n = Compactor.bytes(w <> t)
      +le = Equal.trans(Bool, Nat.is_le(n, 4n+k), Nat.is_le(C.Text.len(w <> t), 4n+k), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 4n+k), n, C.Text.len(w <> t), Equal.sym(Nat, C.Text.len(w <> t), n, LA.lp.len(w <> t))), efit)
      LA.pc.and_true(Nat.is_lt(0n, n), Nat.is_le(n, 4n+k), pc.pos_len(w, t), le)
    case False{} False{}:
      pc.end_fits(best, nb, c, rest, k)
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          ih

def pc.fits_go(tries: Nat, +k: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, nb: pc.NE(best), rs: List<&2, C.Reply>, +c: C.W, +rest: List<&2, C.W>) -> {Compactor.within(4n+k, C.Line.line(C.line.go(tries, 4n+k, best, bl, rs, c <> rest))) == True{} : Bool}:
  match tries:
    case 0n:
      pc.end_fits(best, nb, c, rest, k)
    case 1n+p:
      match rs:
        case Nil{}:
          {==}
        case r <> +more:
          match r:
            case C.Erred{}:
              {==}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  pc.end_fits(best, nb, c, rest, k)
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.fits_next(Nat.is_le(len, 4n+k), C.shorter(len, best, bl), w, t, k, best, nb, c, rest, C.line.go(q, 4n+k, Some{w <> t}, len, more, c <> rest), {==}, pc.fits_go(q, k, Some{w <> t}, len, Unit{}, more, c, rest))

def Compactor.line_fits(tries, k, c, rest, rs):
  pc.fits_go(tries, k, None{}, 0n, Unit{}, rs, c, rest)
