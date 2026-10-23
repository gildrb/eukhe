# eukhe: the proof of LAW line_fits

import Base
import ../../bend/optchat.bend as O
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# a cut fits its room
def pc.cut_le(t: List<&2, C.W>, room: Nat) -> {Nat.is_le(C.Text.len(C.cut(t, room)), room) == True{} : Bool}:
  match t:
    case Nil{}:
      L.compactor.pc.le_zero(room)
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
def pc.cut_fits(c: C.W, t: List<&2, C.W>, k: Nat) -> {C.line.fits(4n+k, Some{C.cut(c <> t, 4n+k)}) == True{} : Bool}:
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

def pc.end_fits(best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, k: Nat) -> {C.line.fits(4n+k, Some{C.line.end(4n+k, best, c <> rest)}) == True{} : Bool}:
  match best:
    case None{}:
      pc.cut_fits(c, rest, k)
    case Some{b}:
      match b:
        case Nil{}:
          match nb:
        case x <> y:
          pc.cut_fits(x, y, k)

def pc.pos_len(w: C.W, -t: List<&2, C.W>) -> {O.Nat.is_pos(C.Text.len(w <> t)) == True{} : Bool}:
  match w:
    case C.W1{}:
      {==}
    case C.W2{}:
      {==}
    case C.W3{}:
      {==}
    case C.W4{}:
      {==}

def pc.fits_next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +k: Nat, best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, rec: C.Line, efit: {Nat.is_le(C.Text.len(w <> t), 4n+k) == fit : Bool}, ih: {C.line.fits(4n+k, C.Line.line(rec)) == True{} : Bool}) -> {C.line.fits(4n+k, C.Line.line(C.line.next(fit, less, w <> t, 4n+k, best, c <> rest, rec))) == True{} : Bool}:
  match fit less:
    case True{} l:
      LA.pc.and_true(O.Nat.is_pos(C.Text.len(w <> t)), Nat.is_le(C.Text.len(w <> t), 4n+k), pc.pos_len(w, t), efit)
    case False{} False{}:
      pc.end_fits(best, nb, c, rest, k)
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          ih

def pc.fits_go(tries: Nat, +k: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, nb: pc.NE(best), rs: List<&2, C.Reply>, +c: C.W, +rest: List<&2, C.W>) -> {C.line.fits(4n+k, C.Line.line(C.line.go(tries, 4n+k, best, bl, rs, c <> rest))) == True{} : Bool}:
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

def pc.line_fits(+tries: Nat, +k: Nat, +c: C.W, +rest: List<&2, C.W>, +rs: List<&2, C.Reply>) -> {C.line.fits(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}:
  pc.fits_go(tries, k, None{}, 0n, Unit{}, rs, c, rest)

def Laws.line_fits(tries, k, c, rest, rs):
  pc.line_fits(tries, k, c, rest, rs)
