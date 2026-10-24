# eukhe: the proof of LAW bound_head_full_keeps: a fill reads only its first k lines, and one that runs out of bytes inside what was stored stops the same on the whole output

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def hf.or_t(a: Bool, e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def hf.lt_not_le(b: Nat, a: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_le(a, b) == False{} : Bool}:
  match b a:
    case 0n 0n:
      LBound.bnd.ft({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+s:
      {==}
    case 1n+r 0n:
      LBound.bnd.ft({Nat.is_le(0n, 1n+r) == False{} : Bool}, h)
    case 1n+r 1n+s:
      hf.lt_not_le(r, s, h)

def hf.lt_le(b: Nat, a: Nat, x: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}, ha: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_lt(b, x) == True{} : Bool}:
  match b a x:
    case 0n 0n x:
      LBound.bnd.ft({Nat.is_lt(0n, x) == True{} : Bool}, h)
    case 0n 1n+s 0n:
      LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, ha)
    case 0n 1n+s 1n+y:
      {==}
    case 1n+r 0n x:
      LBound.bnd.ft({Nat.is_lt(1n+r, x) == True{} : Bool}, h)
    case 1n+r 1n+s 0n:
      LBound.bnd.ft({Nat.is_lt(1n+r, 0n) == True{} : Bool}, ha)
    case 1n+r 1n+s 1n+y:
      hf.lt_le(r, s, y, h, ha)

def hf.lt_sub(y: Nat, b: Nat, +s: Nat, hy: {Nat.is_le(y, b) == True{} : Bool}, h: {Nat.is_lt(b, Nat.add(y, s)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(b, y), s) == True{} : Bool}:
  match y b:
    case 0n +b:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, LBound.bnd.sub_zero(b)) : {Nat.is_lt(_, s) == True{} : Bool}
      h
    case 1n+p 0n:
      LBound.bnd.ft({Nat.is_lt(Nat.sub(0n, 1n+p), s) == True{} : Bool}, hy)
    case 1n+p 1n+q:
      hf.lt_sub(p, q, s, hy, h)

# the budget left after a line that fits is still short of the rest
def hf.prem(+y: Nat, +t: Nat, +p: Nat, +b: Nat, e: {Nat.is_le(y, b) == True{} : Bool}, h: {Nat.is_lt(b, Nat.add(Nat.add(y, t), p)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(b, y), Nat.add(t, p)) == True{} : Bool}:
  hf.lt_sub(y, b, Nat.add(t, p), e, Equal.trans(Bool, Nat.is_lt(b, Nat.add(y, Nat.add(t, p))), Nat.is_lt(b, Nat.add(Nat.add(y, t), p)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(b, z), Nat.add(y, Nat.add(t, p)), Nat.add(Nat.add(y, t), p), Equal.sym(Nat, Nat.add(Nat.add(y, t), p), Nat.add(y, Nat.add(t, p)), LBound.bnd.add_assoc(y, t, p))), h))

def hf.zero(xs: List<&2, Nat>, b: Nat) -> {Bd.fill(xs, 0n, b) == Bd.Win{0n, 0n} : Bd.Win}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      {==}

# a fill reads only its first k lines
def hf.take(ys: List<&2, Nat>, +a: List<&2, Nat>, +z: List<&2, Nat>, k: Nat, +b: Nat, h: {Nat.is_le(k, List.length(&2, Nat, ys)) == True{} : Bool}) -> {Bd.fill(List.append(&2, Nat, ys, a), k, b) == Bd.fill(List.append(&2, Nat, ys, z), k, b) : Bd.Win}:
  match ys:
    case Nil{}:
      match k:
        case 0n:
          Equal.trans(Bd.Win, Bd.fill(a, 0n, b), Bd.Win{0n, 0n}, Bd.fill(z, 0n, b), hf.zero(a, b), Equal.sym(Bd.Win, Bd.fill(z, 0n, b), Bd.Win{0n, 0n}, hf.zero(z, b)))
        case 1n+j:
          LBound.bnd.ft({Bd.fill(a, 1n+j, b) == Bd.fill(z, 1n+j, b) : Bd.Win}, h)
    case +y <> +r:
      match k:
        case 0n:
          {==}
        case 1n++j:
          Equal.cong(Bd.Win, Bd.Win, w => Bd.fill.pick(Nat.is_le(y, b), y, w), Bd.fill(List.append(&2, Nat, r, a), j, Nat.sub(b, y)), Bd.fill(List.append(&2, Nat, r, z), j, Nat.sub(b, y)), hf.take(r, a, z, j, Nat.sub(b, y), h))

def hf.pick(fits: Bool, +y: Nat, +b: Nat, +w1: Bd.Win, +w2: Bd.Win, e: {Nat.is_le(y, b) == fits : Bool}, ih: {Nat.is_le(y, b) == True{} : Bool} -> {w1 == w2 : Bd.Win}) -> {Bd.fill.pick(fits, y, w1) == Bd.fill.pick(fits, y, w2) : Bd.Win}:
  match fits:
    case True{}:
      Equal.cong(Bd.Win, Bd.Win, w => Bd.fill.pick(True{}, y, w), w1, w2, ih(e))
    case False{}:
      {==}

# past the cap's bytes, the stored piece and the whole next line both stop the fill
def hf.last(+q: Nat, +x: Nat, +rest: List<&2, Nat>, k: Nat, +b: Nat, +part: {Nat.is_le(1n+q, x) == True{} : Bool}, +h: {Nat.is_lt(b, 1n+q) == True{} : Bool}) -> {Bd.fill([1n+q], k, b) == Bd.fill(x <> rest, k, b) : Bd.Win}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Bool, Nat.is_le(1n+q, b), False{}, hf.lt_not_le(b, 1n+q, h)) : {Bd.fill.pick(_, 1n+q, Bd.fill(Nil{}, j, Nat.sub(b, 1n+q))) == Bd.fill.pick(Nat.is_le(x, b), x, Bd.fill(rest, j, Nat.sub(b, x))) : Bd.Win}
      %Equal.sym(Bool, Nat.is_le(x, b), False{}, hf.lt_not_le(b, x, hf.lt_le(b, 1n+q, x, h, part))) : {Bd.fill.pick(False{}, 1n+q, Bd.fill(Nil{}, j, Nat.sub(b, 1n+q))) == Bd.fill.pick(_, x, Bd.fill(rest, j, Nat.sub(b, x))) : Bd.Win}
      {==}

# a fill that runs out of bytes before the end of what a head stored stops the same on the whole output
def hf.over(ys: List<&2, Nat>, +p: Nat, +x: Nat, +rest: List<&2, Nat>, k: Nat, +b: Nat, +part: {Nat.is_le(p, x) == True{} : Bool}, h: {Nat.is_lt(b, Nat.add(Bound.bd_total(ys), p)) == True{} : Bool}) -> {Bd.fill(List.append(&2, Nat, ys, Bound.bd_part(p)), k, b) == Bd.fill(List.append(&2, Nat, ys, x <> rest), k, b) : Bd.Win}:
  match ys:
    case Nil{}:
      match p:
        case 0n:
          match b:
            case 0n:
              LBound.bnd.ft({Bd.fill(Nil{}, k, 0n) == Bd.fill(x <> rest, k, 0n) : Bd.Win}, h)
            case 1n+r:
              LBound.bnd.ft({Bd.fill(Nil{}, k, 1n+r) == Bd.fill(x <> rest, k, 1n+r) : Bd.Win}, h)
        case 1n+q:
          hf.last(q, x, rest, k, b, part, h)
    case +y <> +r:
      match k:
        case 0n:
          {==}
        case 1n++j:
          hf.pick(Nat.is_le(y, b), y, b, Bd.fill(List.append(&2, Nat, r, Bound.bd_part(p)), j, Nat.sub(b, y)), Bd.fill(List.append(&2, Nat, r, x <> rest), j, Nat.sub(b, y)), {==}, e => hf.over(r, p, x, rest, j, Nat.sub(b, y), part, hf.prem(y, Bound.bd_total(r), p, b, e, h)))

# what a head stored is not empty, and the whole output is not either: a line that does not fit is cut the same
def hf.of(w: Bd.Win, ys: List<&2, Nat>, p: Nat, +x: Nat, +rest: List<&2, Nat>, +c: Nat, ne: {Nat.is_lt(0n, Nat.add(List.length(&2, Nat, ys), p)) == True{} : Bool}) -> {Bd.keep.of(w, List.append(&2, Nat, ys, Bound.bd_part(p)), c) == Bd.keep.of(w, List.append(&2, Nat, ys, x <> rest), c) : Bd.Win}:
  match w:
    case Bd.Win{wb, wl}:
      match wl:
        case 0n:
          match ys:
            case Nil{}:
              match p:
                case 0n:
                  LBound.bnd.ft({Bd.keep.of(Bd.Win{wb, 0n}, Nil{}, c) == Bd.keep.of(Bd.Win{wb, 0n}, x <> rest, c) : Bd.Win}, ne)
                case 1n+q:
                  {==}
            case +y <> +r:
              {==}
        case 1n+m:
          {==}

def hf.ne_bytes(ys: List<&2, Nat>, p: Nat, b: Nat, h: {Nat.is_lt(b, Nat.add(Bound.bd_total(ys), p)) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(List.length(&2, Nat, ys), p)) == True{} : Bool}:
  match ys:
    case Nil{}:
      match p:
        case 0n:
          match b:
            case 0n:
              LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
            case 1n+r:
              LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
        case 1n+q:
          {==}
    case +y <> +r:
      {==}

def hf.ne_lines(ys: List<&2, Nat>, p: Nat, j: Nat, h: {Nat.is_le(1n+j, List.length(&2, Nat, ys)) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(List.length(&2, Nat, ys), p)) == True{} : Bool}:
  match ys:
    case Nil{}:
      LBound.bnd.ft({Nat.is_lt(0n, Nat.add(0n, p)) == True{} : Bool}, h)
    case +y <> +r:
      {==}

def hf.full(lf: Bool, +ys: List<&2, Nat>, +p: Nat, +x: Nat, +rest: List<&2, Nat>, +j: Nat, +q: Nat, +c: Nat, +part: {Nat.is_le(p, x) == True{} : Bool}, +el: {Nat.is_le(1n+j, List.length(&2, Nat, ys)) == lf : Bool}, full: {Bool.or(Nat.is_lt(1n+q, Nat.add(Bound.bd_total(ys), p)), lf) == True{} : Bool}) -> {Bd.keep(List.append(&2, Nat, ys, Bound.bd_part(p)), 1n+j, 1n+q, c) == Bd.keep(List.append(&2, Nat, ys, x <> rest), 1n+j, 1n+q, c) : Bd.Win}:
  match lf:
    case True{}:
      +s = List.append(&2, Nat, ys, Bound.bd_part(p))
      +wh = List.append(&2, Nat, ys, x <> rest)
      %Equal.sym(Bd.Win, Bd.fill(s, 1n+j, 1n+q), Bd.fill(wh, 1n+j, 1n+q), hf.take(ys, Bound.bd_part(p), x <> rest, 1n+j, 1n+q, el)) : {Bd.keep.of(_, s, c) == Bd.keep.of(Bd.fill(wh, 1n+j, 1n+q), wh, c) : Bd.Win}
      hf.of(Bd.fill(wh, 1n+j, 1n+q), ys, p, x, rest, c, hf.ne_lines(ys, p, j, el))
    case False{}:
      +s = List.append(&2, Nat, ys, Bound.bd_part(p))
      +wh = List.append(&2, Nat, ys, x <> rest)
      +hb = hf.or_t(Nat.is_lt(1n+q, Nat.add(Bound.bd_total(ys), p)), full)
      %Equal.sym(Bd.Win, Bd.fill(s, 1n+j, 1n+q), Bd.fill(wh, 1n+j, 1n+q), hf.over(ys, p, x, rest, 1n+j, 1n+q, part, hb)) : {Bd.keep.of(_, s, c) == Bd.keep.of(Bd.fill(wh, 1n+j, 1n+q), wh, c) : Bd.Win}
      hf.of(Bd.fill(wh, 1n+j, 1n+q), ys, p, x, rest, c, hf.ne_bytes(ys, p, 1n+q, hb))

def Bound.bound_head_full_keeps(ys, p, x, rest, k, b, c, part, full):
  match k:
    case 0n:
      {==}
    case 1n++j:
      match b:
        case 0n:
          {==}
        case 1n++q:
          hf.full(Nat.is_le(1n+j, List.length(&2, Nat, ys)), ys, p, x, rest, j, q, c, part, {==}, full)
