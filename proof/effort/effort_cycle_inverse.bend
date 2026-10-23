# eukhe: the proof of LAW effort_cycle_inverse

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

# backward undoes forward on an ascending pre ++ [l] ++ post
def pe.bf(pre: List<&2, Ef.Lv>, +l: Ef.Lv, post: List<&2, Ef.Lv>, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, l <> post)) == True{} : Bool}) -> {LA.pe.tl(List.append(&2, Ef.Lv, pre, l <> post), LA.pe.tl(List.append(&2, Ef.Lv, pre, l <> post), l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  match pre:
    case Nil{}:
      match post:
        case Nil{}:
          {==}
        case +b <> +q:
          LA.pe.tl_two(l <> b <> q, l, b, Ef.Forward{}, Ef.Backward{}, LA.pe.next(Nil{}, l, b, q, h), LA.pe.prev(Nil{}, l, b, q, h))
    case +x <> +r:
      match post:
        case Nil{}:
          LA.pe.tl_two(List.append(&2, Ef.Lv, x <> r, [l]), l, x, Ef.Forward{}, Ef.Backward{}, LA.pe.wrap(x, r, l, h), LA.pe.wrap_back(x, r, l))
        case +b <> +q:
          LA.pe.tl_two(List.append(&2, Ef.Lv, x <> r, l <> b <> q), l, b, Ef.Forward{}, Ef.Backward{}, LA.pe.next(x <> r, l, b, q, h), LA.pe.prev(x <> r, l, b, q, h))

def pe.bf_any(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.asc(lad) == True{} : Bool}, in: {Ef.has(lad, l) == True{} : Bool}) -> {LA.pe.tl(lad, LA.pe.tl(lad, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  +pre = LA.pe.spre(lad, l, Ef.at(lad, l))
  +post = LA.pe.spost(lad, l, Ef.at(lad, l))
  +e = LA.pe.split(lad, l, Ef.at(lad, l), {==}, in)
  %Equal.sym(List<&2, Ef.Lv>, lad, List.append(&2, Ef.Lv, pre, l <> post), e) : {LA.pe.tl(_, LA.pe.tl(_, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}
  pe.bf(pre, l, post, LA.pe.asc_tr(lad, List.append(&2, Ef.Lv, pre, l <> post), e, h))

def pe.effort_cycle_inverse(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.turn(m, Ef.turn(m, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}:
  pe.bf_any(Ef.offered(m), l, LA.pe.effort_offered_asc(m), in)

def Laws.effort_cycle_inverse(m, l, in):
  pe.effort_cycle_inverse(m, l, in)
