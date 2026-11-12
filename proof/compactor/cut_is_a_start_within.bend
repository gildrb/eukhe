# eukhe: the proof of LAW cut_is_a_start_within
# The rest is what the cut leaves (ccs.rest, character by character as
# cut goes): the cut then the rest is the text (ccs.app), and each
# character the cut keeps fits what is left of the room (ccs.le).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

# what a cut to room bytes leaves of t
def ccs.rest(t: List<&2, C.W>, room: Nat) -> List<&2, C.W>:
  match t:
    case Nil{}:
      Nil{}
    case c <> more:
      match c room:
        case C.W1{} 0n:
          C.W1{} <> more
        case C.W1{} 1n+r:
          ccs.rest(more, r)
        case C.W2{} 0n:
          C.W2{} <> more
        case C.W2{} 1n:
          C.W2{} <> more
        case C.W2{} 2n+r:
          ccs.rest(more, r)
        case C.W3{} 0n:
          C.W3{} <> more
        case C.W3{} 1n:
          C.W3{} <> more
        case C.W3{} 2n:
          C.W3{} <> more
        case C.W3{} 3n+r:
          ccs.rest(more, r)
        case C.W4{} 0n:
          C.W4{} <> more
        case C.W4{} 1n:
          C.W4{} <> more
        case C.W4{} 2n:
          C.W4{} <> more
        case C.W4{} 3n:
          C.W4{} <> more
        case C.W4{} 4n+r:
          ccs.rest(more, r)

def ccs.app(t: List<&2, C.W>, room: Nat) -> {List.append(&2, C.W, C.cut(t, room), ccs.rest(t, room)) == t : List<&2, C.W>}:
  match t:
    case Nil{}:
      {==}
    case c <> more:
      match c room:
        case C.W1{} 0n:
          {==}
        case C.W1{} 1n+r:
          Equal.cong(List<&2, C.W>, List<&2, C.W>, z => C.W1{} <> z, List.append(&2, C.W, C.cut(more, r), ccs.rest(more, r)), more, ccs.app(more, r))
        case C.W2{} 0n:
          {==}
        case C.W2{} 1n:
          {==}
        case C.W2{} 2n+r:
          Equal.cong(List<&2, C.W>, List<&2, C.W>, z => C.W2{} <> z, List.append(&2, C.W, C.cut(more, r), ccs.rest(more, r)), more, ccs.app(more, r))
        case C.W3{} 0n:
          {==}
        case C.W3{} 1n:
          {==}
        case C.W3{} 2n:
          {==}
        case C.W3{} 3n+r:
          Equal.cong(List<&2, C.W>, List<&2, C.W>, z => C.W3{} <> z, List.append(&2, C.W, C.cut(more, r), ccs.rest(more, r)), more, ccs.app(more, r))
        case C.W4{} 0n:
          {==}
        case C.W4{} 1n:
          {==}
        case C.W4{} 2n:
          {==}
        case C.W4{} 3n:
          {==}
        case C.W4{} 4n+r:
          Equal.cong(List<&2, C.W>, List<&2, C.W>, z => C.W4{} <> z, List.append(&2, C.W, C.cut(more, r), ccs.rest(more, r)), more, ccs.app(more, r))

def ccs.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ccs.le(t: List<&2, C.W>, room: Nat) -> {Nat.is_le(Compactor.bytes(C.cut(t, room)), room) == True{} : Bool}:
  match t:
    case Nil{}:
      ccs.le0(room)
    case c <> more:
      match c room:
        case C.W1{} 0n:
          {==}
        case C.W1{} 1n+r:
          ccs.le(more, r)
        case C.W2{} 0n:
          {==}
        case C.W2{} 1n:
          {==}
        case C.W2{} 2n+r:
          ccs.le(more, r)
        case C.W3{} 0n:
          {==}
        case C.W3{} 1n:
          {==}
        case C.W3{} 2n:
          {==}
        case C.W3{} 3n+r:
          ccs.le(more, r)
        case C.W4{} 0n:
          {==}
        case C.W4{} 1n:
          {==}
        case C.W4{} 2n:
          {==}
        case C.W4{} 3n:
          {==}
        case C.W4{} 4n+r:
          ccs.le(more, r)

def Compactor.cut_is_a_start_within(t, room):
  +rest = ccs.rest(t, room)
  +cut = C.cut(t, room)
  +e1 = Equal.sym(List<&2, C.W>, List.append(&2, C.W, cut, rest), t, ccs.app(t, room))
  +e2 = Equal.sym(Bool, Nat.is_le(Compactor.bytes(cut), room), True{}, ccs.le(t, room))
  (rest, Equal.trans(List<&2, C.W> & Bool, (List.append(&2, C.W, cut, rest), Nat.is_le(Compactor.bytes(cut), room)), (t, Nat.is_le(Compactor.bytes(cut), room)), (t, True{}),
    Equal.cong(List<&2, C.W>, List<&2, C.W> & Bool, z => (z, Nat.is_le(Compactor.bytes(cut), room)), List.append(&2, C.W, cut, rest), t, Equal.sym(List<&2, C.W>, t, List.append(&2, C.W, cut, rest), e1)),
    Equal.cong(Bool, List<&2, C.W> & Bool, z => (t, z), Nat.is_le(Compactor.bytes(cut), room), True{}, Equal.sym(Bool, True{}, Nat.is_le(Compactor.bytes(cut), room), e2))))
