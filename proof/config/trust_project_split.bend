# eukhe: the proof of LAW trust_project_split
# The items of two runs of keys are the items of each; the values that
# apply of two runs of items are those of the first over nothing, then
# those of the second over the global values. Inductions on the first run.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def pts.item(s: Cf.Scope, k: Nat, v: Nat, a: List<&2, Cf.Item>, b: List<&2, Cf.Item>) -> {Cf.item.of(s, k, v, List.append(&2, Cf.Item, a, b)) == List.append(&2, Cf.Item, Cf.item.of(s, k, v, a), b) : List<&2, Cf.Item>}:
  match s:
    case Cf.Proj{c}:
      {==}
    case Cf.GlobalOnly{}:
      {==}

# the items of two runs of keys are the items of each
def pts.items(xs: List<&2, Cf.PKey>, +ys: List<&2, Cf.PKey>) -> {Cf.items(List.append(&2, Cf.PKey, xs, ys)) == List.append(&2, Cf.Item, Cf.items(xs), Cf.items(ys)) : List<&2, Cf.Item>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case Cf.PKey{+k, +p, +v}:
          %Equal.sym(List<&2, Cf.Item>, Cf.items(List.append(&2, Cf.PKey, t, ys)), List.append(&2, Cf.Item, Cf.items(t), Cf.items(ys)), pts.items(t, ys)) : {Cf.item.of(Cf.Hit.scope(Cf.classify(p)), k, v, _) == List.append(&2, Cf.Item, Cf.item.of(Cf.Hit.scope(Cf.classify(p)), k, v, Cf.items(t)), Cf.items(ys)) : List<&2, Cf.Item>}
          pts.item(Cf.Hit.scope(Cf.classify(p)), k, v, Cf.items(t), Cf.items(ys))

def pts.guard(b: Bool, e: Cf.Entry, a: List<&2, Cf.Entry>, c: List<&2, Cf.Entry>) -> {Cf.guard(b, e, List.append(&2, Cf.Entry, a, c)) == List.append(&2, Cf.Entry, Cf.guard(b, e, a), c) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the values of two runs of items
def pts.eff(+t: Cf.Trust, +g: List<&2, Cf.Entry>, a: List<&2, Cf.Item>, +b: List<&2, Cf.Item>) -> {Cf.effective(t, g, List.append(&2, Cf.Item, a, b)) == List.append(&2, Cf.Entry, Cf.effective(t, Nil{}, a), Cf.effective(t, g, b)) : List<&2, Cf.Entry>}:
  match a:
    case Nil{}:
      {==}
    case i <> +rest:
      match i:
        case Cf.Item{+k, +c, +v}:
          %Equal.sym(List<&2, Cf.Entry>, Cf.effective(t, g, List.append(&2, Cf.Item, rest, b)), List.append(&2, Cf.Entry, Cf.effective(t, Nil{}, rest), Cf.effective(t, g, b)), pts.eff(t, g, rest, b)) : {Cf.guard(Cf.admits(t, c), Cf.Entry{k, v}, _) == List.append(&2, Cf.Entry, Cf.guard(Cf.admits(t, c), Cf.Entry{k, v}, Cf.effective(t, Nil{}, rest)), Cf.effective(t, g, b)) : List<&2, Cf.Entry>}
          pts.guard(Cf.admits(t, c), Cf.Entry{k, v}, Cf.effective(t, Nil{}, rest), Cf.effective(t, g, b))

def Config.trust_project_split(t, g, xs, ys):
  %Equal.sym(List<&2, Cf.Item>, Cf.items(List.append(&2, Cf.PKey, xs, ys)), List.append(&2, Cf.Item, Cf.items(xs), Cf.items(ys)), pts.items(xs, ys)) : {Cf.effective(t, g, _) == List.append(&2, Cf.Entry, Cf.project(t, Nil{}, xs), Cf.project(t, g, ys)) : List<&2, Cf.Entry>}
  pts.eff(t, g, Cf.items(xs), Cf.items(ys))
