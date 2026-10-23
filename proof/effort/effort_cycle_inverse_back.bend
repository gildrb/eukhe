# eukhe: the proof of LAW effort_cycle_inverse_back

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pe.app_snoc(xs: List<&2, Ef.Lv>, +a: Ef.Lv, +ys: List<&2, Ef.Lv>) -> {List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, xs, [a]), ys) == List.append(&2, Ef.Lv, xs, a <> ys) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, zs => x <> zs, List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, r, [a]), ys), List.append(&2, Ef.Lv, r, a <> ys), pe.app_snoc(r, a, ys))

# x <> r without its last level
def pe.init(r: List<&2, Ef.Lv>, x: Ef.Lv) -> List<&2, Ef.Lv>:
  match r:
    case Nil{}:
      Nil{}
    case y <> s:
      x <> pe.init(s, y)

def pe.init_last(r: List<&2, Ef.Lv>, +x: Ef.Lv) -> {x <> r == List.append(&2, Ef.Lv, pe.init(r, x), [Ef.last(r, x)]) : List<&2, Ef.Lv>}:
  match r:
    case Nil{}:
      {==}
    case +y <> +s:
      Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, zs => x <> zs, y <> s, List.append(&2, Ef.Lv, pe.init(s, y), [Ef.last(s, y)]), pe.init_last(s, y))

# forward undoes backward on an ascending pre ++ [l] ++ post
def pe.fb(pre: List<&2, Ef.Lv>, +l: Ef.Lv, +post: List<&2, Ef.Lv>, +h: {Ef.asc(List.append(&2, Ef.Lv, pre, l <> post)) == True{} : Bool}) -> {LA.pe.tl(List.append(&2, Ef.Lv, pre, l <> post), LA.pe.tl(List.append(&2, Ef.Lv, pre, l <> post), l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  match pre:
    case Nil{}:
      match post:
        case Nil{}:
          {==}
        case +p <> +ps:
          +i = pe.init(ps, p)
          +z = Ef.last(ps, p)
          +e = pe.init_last(ps, p)
          %Equal.sym(List<&2, Ef.Lv>, p <> ps, List.append(&2, Ef.Lv, i, [z]), e) : {LA.pe.tl(l <> _, LA.pe.tl(l <> _, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
          +h2 = LA.pe.asc_tr(l <> p <> ps, l <> List.append(&2, Ef.Lv, i, [z]), Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, ys => l <> ys, p <> ps, List.append(&2, Ef.Lv, i, [z]), e), h)
          LA.pe.tl_two(List.append(&2, Ef.Lv, l <> i, [z]), l, z, Ef.Backward{}, Ef.Forward{}, LA.pe.wrap_back(l, i, z), LA.pe.wrap(l, i, z, h2))
    case +x <> +r:
      +i = pe.init(r, x)
      +a = Ef.last(r, x)
      +tail = {l <> post : List<&2, Ef.Lv>}
      +c1 = Equal.cong(List<&2, Ef.Lv>, List<&2, Ef.Lv>, ys => List.append(&2, Ef.Lv, ys, tail), x <> r, List.append(&2, Ef.Lv, i, [a]), pe.init_last(r, x))
      +e = Equal.trans(List<&2, Ef.Lv>, List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, List.append(&2, Ef.Lv, i, [a]), tail), List.append(&2, Ef.Lv, i, a <> tail), c1, pe.app_snoc(i, a, tail))
      %Equal.sym(List<&2, Ef.Lv>, List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, i, a <> tail), e) : {LA.pe.tl(_, LA.pe.tl(_, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
      +h2 = LA.pe.asc_tr(List.append(&2, Ef.Lv, x <> r, tail), List.append(&2, Ef.Lv, i, a <> tail), e, h)
      LA.pe.tl_two(List.append(&2, Ef.Lv, i, a <> l <> post), l, a, Ef.Backward{}, Ef.Forward{}, LA.pe.prev(i, a, l, post, h2), LA.pe.next(i, a, l, post, h2))

def pe.fb_any(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.asc(lad) == True{} : Bool}, in: {Ef.has(lad, l) == True{} : Bool}) -> {LA.pe.tl(lad, LA.pe.tl(lad, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  +pre = LA.pe.spre(lad, l, Ef.at(lad, l))
  +post = LA.pe.spost(lad, l, Ef.at(lad, l))
  +e = LA.pe.split(lad, l, Ef.at(lad, l), {==}, in)
  %Equal.sym(List<&2, Ef.Lv>, lad, List.append(&2, Ef.Lv, pre, l <> post), e) : {LA.pe.tl(_, LA.pe.tl(_, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}
  pe.fb(pre, l, post, LA.pe.asc_tr(lad, List.append(&2, Ef.Lv, pre, l <> post), e, h))

def pe.effort_cycle_inverse_back(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.turn(m, Ef.turn(m, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}:
  pe.fb_any(Ef.offered(m), l, LA.pe.effort_offered_asc(m), in)

def Effort.effort_cycle_inverse_back(m, l, in):
  pe.effort_cycle_inverse_back(m, l, in)
