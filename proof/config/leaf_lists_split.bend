# eukhe: the proof of LAW leaf_lists_split
# An induction on the first run: each leaf adds its path to one list.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def pls.Two(xs: List<&2, Cf.Leaf>, ys: List<&2, Cf.Leaf>) -> Type:
  {Cf.applied(List.append(&2, Cf.Leaf, xs, ys)) == List.append(&2, Nat, Cf.applied(xs), Cf.applied(ys)) : List<&2, Nat>} & {Cf.reported(List.append(&2, Cf.Leaf, xs, ys)) == List.append(&2, Nat, Cf.reported(xs), Cf.reported(ys)) : List<&2, Nat>}

# a good leaf adds its path to the applied list
def pls.good(+p: Nat, +t: List<&2, Cf.Leaf>, +ys: List<&2, Cf.Leaf>, ih: pls.Two(t, ys)) -> pls.Two(Cf.Leaf{p, Cf.Good{}} <> t, ys):
  (ea, er) = ih
  (Equal.cong(List<&2, Nat>, List<&2, Nat>, z => p <> z, Cf.applied(List.append(&2, Cf.Leaf, t, ys)), List.append(&2, Nat, Cf.applied(t), Cf.applied(ys)), ea), er)

# a leaf that is not good adds its path to the reported list
def pls.bad(+p: Nat, o: Cf.Outcome, +t: List<&2, Cf.Leaf>, +ys: List<&2, Cf.Leaf>, ih: pls.Two(t, ys), ea: {Cf.applied(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)) == Cf.applied(List.append(&2, Cf.Leaf, t, ys)) : List<&2, Nat>}, eb: {Cf.reported(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)) == p <> Cf.reported(List.append(&2, Cf.Leaf, t, ys)) : List<&2, Nat>}) -> ({Cf.applied(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)) == List.append(&2, Nat, Cf.applied(t), Cf.applied(ys)) : List<&2, Nat>} & {Cf.reported(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)) == p <> List.append(&2, Nat, Cf.reported(t), Cf.reported(ys)) : List<&2, Nat>}):
  (ia, ir) = ih
  (Equal.trans(List<&2, Nat>, Cf.applied(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)), Cf.applied(List.append(&2, Cf.Leaf, t, ys)), List.append(&2, Nat, Cf.applied(t), Cf.applied(ys)), ea, ia),
    Equal.trans(List<&2, Nat>, Cf.reported(List.append(&2, Cf.Leaf, Cf.Leaf{p, o} <> t, ys)), p <> Cf.reported(List.append(&2, Cf.Leaf, t, ys)), p <> List.append(&2, Nat, Cf.reported(t), Cf.reported(ys)), eb, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => p <> z, Cf.reported(List.append(&2, Cf.Leaf, t, ys)), List.append(&2, Nat, Cf.reported(t), Cf.reported(ys)), ir)))

def Config.leaf_lists_split(xs, ys):
  match xs:
    case Nil{}:
      ({==}, {==})
    case l <> +t:
      match l:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              pls.good(p, t, ys, Config.leaf_lists_split(t, ys))
            case Cf.BadType{}:
              pls.bad(p, Cf.BadType{}, t, ys, Config.leaf_lists_split(t, ys), {==}, {==})
            case Cf.Undeclared{}:
              pls.bad(p, Cf.Undeclared{}, t, ys, Config.leaf_lists_split(t, ys), {==}, {==})
