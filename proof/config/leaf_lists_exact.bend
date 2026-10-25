# eukhe: the proof of LAW leaf_lists_exact
# Both lists are built leaf by leaf, in order: an induction on the leaves.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def pll.good(ls: List<&2, Cf.Leaf>) -> {Cf.applied(ls) == Config.cf_good_paths(ls) : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              %pll.good(rest) : {p <> Cf.applied(rest) == p <> _ : List<&2, Nat>}
              {==}
            case Cf.BadType{}:
              pll.good(rest)
            case Cf.Undeclared{}:
              pll.good(rest)

def pll.bad(ls: List<&2, Cf.Leaf>) -> {Cf.reported(ls) == Config.cf_bad_paths(ls) : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              pll.bad(rest)
            case Cf.BadType{}:
              %pll.bad(rest) : {p <> Cf.reported(rest) == p <> _ : List<&2, Nat>}
              {==}
            case Cf.Undeclared{}:
              %pll.bad(rest) : {p <> Cf.reported(rest) == p <> _ : List<&2, Nat>}
              {==}

def Config.leaf_lists_exact(ls):
  (pll.good(ls), pll.bad(ls))
