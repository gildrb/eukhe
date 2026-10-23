# eukhe: lemmas the proofs of area tree share: tree/put

import Base
import ../../../../bend/tree.bend as Tr
import ../logic.bend as LALogic
import ../pair.bend as LAPair
import ./KMap.bend as LATreeKMap

def tc.put_case_mpok(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == True{} : Bool}:
  match b:
    case True{}:
      LATreeKMap.tc.set_mpok(m, hs, e, mk)
    case False{}:
      mk

def tc.rec_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +mk: {LALogic.tc.mpok(m) == True{} : Bool}) -> {LALogic.tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          tc.put_case_mpok(Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))), m, hs, Tr.Ent{k, p, v}, mk)
        case Tr.Del{x}:
          match x:
            case 0n:
              mk
            case 1n++y:
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              LATreeKMap.tc.drop_mpok(Tr.drops(F, hs, 1n+y), m, mk)
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      LAPair.tc.keep_case_bst2(Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n), m, n, mk, LATreeKMap.tc.patch_mpok(ops, hs, m, mk))
