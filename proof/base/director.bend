# eukhe: lemmas the proofs of two or more areas share: director

import Base
import ../../bend/director.bend as Dr
import ../../bend/tree.bend as Tr
import ./list.bend as LList

# Resume and rewind
# -----------------

# decode reads the layers of encode(s) back onto acc, then goes on
def pd.dec_go(s: List<&2, Dr.Layer>, +B: List<&2, Tr.Ent>, +acc: List<&2, Dr.Layer>) -> {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), B), acc) == Dr.decode.go(B, List.append(&2, Dr.Layer, s, acc)) : List<&2, Dr.Layer>}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +E = Dr.encode(rest)
          %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E, [x, y]), B), List.append(&2, Tr.Ent, E, x <> y <> B), LList.pd.app_assoc(Tr.Ent, E, [x, y], B)) : {Dr.decode.go(_, acc) == Dr.decode.go(B, Dr.Layer{k, b} <> List.append(&2, Dr.Layer, rest, acc)) : List<&2, Dr.Layer>}
          pd.dec_go(rest, x <> y <> B, acc)

def pd.dir_resume_restores(+s: List<&2, Dr.Layer>) -> {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}:
  %LList.pd.app_nil(Tr.Ent, Dr.encode(s)) : {Dr.decode.go(_, Nil{}) == s : List<&2, Dr.Layer>}
  %LList.pd.app_nil(Dr.Layer, s) : {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), Nil{}), Nil{}) == _ : List<&2, Dr.Layer>}
  pd.dec_go(s, Nil{}, Nil{})
