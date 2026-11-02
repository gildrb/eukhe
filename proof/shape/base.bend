# eukhe: lemmas shared by the proofs of area shape: logic and lists of
# places.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape

# Logic
# -----

def shb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise True == False proves anything
def shb.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : shb.IfT(_, G)
  Unit{}

# Lists of places
# ---------------

def shb.app_nil(xs: List<&2, S.St>) -> {List.append(&2, S.St, xs, Nil{}) == xs : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      Equal.cong(List<&2, S.St>, List<&2, S.St>, r => x <> r, List.append(&2, S.St, t, Nil{}), t, shb.app_nil(t))

def shb.app_assoc(xs: List<&2, S.St>, +ys: List<&2, S.St>, +zs: List<&2, S.St>) -> {List.append(&2, S.St, List.append(&2, S.St, xs, ys), zs) == List.append(&2, S.St, xs, List.append(&2, S.St, ys, zs)) : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      Equal.cong(List<&2, S.St>, List<&2, S.St>, r => x <> r, List.append(&2, S.St, List.append(&2, S.St, t, ys), zs), List.append(&2, S.St, t, List.append(&2, S.St, ys, zs)), shb.app_assoc(t, ys, zs))

# the first place of a list, as a list
def shb.take1(xs: List<&2, S.St>) -> List<&2, S.St>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      [x]

# the end condition distributes over a list's halves
def shb.keep_app(e: Bool, xs: List<&2, S.St>, +ys: List<&2, S.St>) -> {Shape.sp_keep(e, List.append(&2, S.St, xs, ys)) == List.append(&2, S.St, Shape.sp_keep(e, xs), Shape.sp_keep(e, ys)) : List<&2, S.St>}:
  match e:
    case False{}:
      {==}
    case True{}:
      match xs:
        case Nil{}:
          {==}
        case x <> +t:
          +y = x
          +a = Shape.sp_if(String.is_empty(Shape.sp_text(y)), [y])
          %Equal.sym(List<&2, S.St>, Shape.sp_keep(True{}, List.append(&2, S.St, t, ys)), List.append(&2, S.St, Shape.sp_keep(True{}, t), Shape.sp_keep(True{}, ys)), shb.keep_app(True{}, t, ys)) : {List.append(&2, S.St, a, _) == List.append(&2, S.St, List.append(&2, S.St, a, Shape.sp_keep(True{}, t)), Shape.sp_keep(True{}, ys)) : List<&2, S.St>}
          Equal.sym(List<&2, S.St>, List.append(&2, S.St, List.append(&2, S.St, a, Shape.sp_keep(True{}, t)), Shape.sp_keep(True{}, ys)), List.append(&2, S.St, a, List.append(&2, S.St, Shape.sp_keep(True{}, t), Shape.sp_keep(True{}, ys))), shb.app_assoc(a, Shape.sp_keep(True{}, t), Shape.sp_keep(True{}, ys)))

# the first of no readings is none
def shb.take1_nil(e: Bool) -> {Nil{} == shb.take1(Shape.sp_keep(e, Nil{})) : List<&2, S.St>}:
  match e:
    case False{}:
      {==}
    case True{}:
      {==}
