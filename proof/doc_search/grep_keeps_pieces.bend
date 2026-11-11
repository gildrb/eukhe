# eukhe: the proof of LAW grep_keeps_pieces
#
# PROOF: by induction on es: an entry leaves rem less what it kept
# (kp.left), and taking off its count then the rest's is taking off their
# sum (ds.sub_sub).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

# an entry leaves rem less what it kept
def kp.left(e: Sr.Ent, +p: Nat, +rem: Nat) -> {Sr.left(e, p, rem) == Nat.sub(rem, Sr.kept(e, p, rem)) : Nat}:
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          {==}
        case Sr.Skip{w}:
          Equal.sym(Nat, Nat.sub(rem, 0n), rem, LA.ds.sub_zero(rem))

def kp.go(es: List<&2, Sr.Ent>, +fs: List<&2, Sr.Ent>, +p: Nat, +rem: Nat) -> {Sr.keeps(List.append(&2, Sr.Ent, es, fs), p, rem) == List.append(&2, Nat, Sr.keeps(es, p, rem), Sr.keeps(fs, p, Nat.sub(rem, DocSearch.ds_sum(Sr.keeps(es, p, rem))))) : List<&2, Nat>}:
  match es:
    case Nil{}:
      %Equal.sym(Nat, Nat.sub(rem, 0n), rem, LA.ds.sub_zero(rem)) : {Sr.keeps(fs, p, rem) == Sr.keeps(fs, p, _) : List<&2, Nat>}
      {==}
    case +e <> +r:
      +l = Sr.left(e, p, rem)
      +x = Sr.kept(e, p, rem)
      +a = Sr.keeps(r, p, l)
      +s = DocSearch.ds_sum(a)
      %Equal.sym(List<&2, Nat>, Sr.keeps(List.append(&2, Sr.Ent, r, fs), p, l), List.append(&2, Nat, a, Sr.keeps(fs, p, Nat.sub(l, s))), kp.go(r, fs, p, l)) : {x <> _ == x <> List.append(&2, Nat, a, Sr.keeps(fs, p, Nat.sub(rem, Nat.add(x, s)))) : List<&2, Nat>}
      %LA.ds.sub_sub(rem, x, s) : {x <> List.append(&2, Nat, a, Sr.keeps(fs, p, Nat.sub(l, s))) == x <> List.append(&2, Nat, a, Sr.keeps(fs, p, _)) : List<&2, Nat>}
      %kp.left(e, p, rem) : {x <> List.append(&2, Nat, a, Sr.keeps(fs, p, Nat.sub(l, s))) == x <> List.append(&2, Nat, a, Sr.keeps(fs, p, Nat.sub(_, s))) : List<&2, Nat>}
      {==}

def DocSearch.grep_keeps_pieces(es, fs, e, p, rem):
  (kp.go(es, fs, p, rem), {==})
