# eukhe: the proof of LAW cut_longest
# Induction on the start p: its first character fits the room (p fits),
# so the cut keeps that character too and goes on with the room left.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

def ccl.go(p: List<&2, C.W>, +q: List<&2, C.W>, room: Nat, fit: {Nat.is_le(Compactor.bytes(p), room) == True{} : Bool}) -> {Nat.is_le(List.length(&2, C.W, p), List.length(&2, C.W, C.cut(List.append(&2, C.W, p, q), room))) == True{} : Bool}:
  match p:
    case Nil{}:
      LNat.compactor.pc.le_zero(List.length(&2, C.W, C.cut(q, room)))
    case c <> more:
      match c room:
        case C.W1{} 0n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W1{} 1n+r:
          ccl.go(more, q, r, fit)
        case C.W2{} 0n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W2{} 1n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W2{} 2n+r:
          ccl.go(more, q, r, fit)
        case C.W3{} 0n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W3{} 1n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W3{} 2n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W3{} 3n+r:
          ccl.go(more, q, r, fit)
        case C.W4{} 0n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W4{} 1n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W4{} 2n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W4{} 3n:
          LLogicLogic.pc.absurd_ft({Nat.is_le(1n+List.length(&2, C.W, more), 0n) == True{} : Bool}, fit)
        case C.W4{} 4n+r:
          ccl.go(more, q, r, fit)

def Compactor.cut_longest(p, q, room, fit):
  ccl.go(p, q, room, fit)
