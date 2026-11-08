# eukhe: the proof of LAW distinct_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def pd.path(l: Cf.Leaf) -> {Cf.Leaf.path(l) == CR.cr_path(l) : Nat}:
  match l:
    case Cf.Leaf{p, o}:
      {==}

# a path among the leaves' paths is a path of a leaf
def pd.in(ls: List<&2, Cf.Leaf>, +n: Nat) -> {Cf.listed(Cf.paths(ls), n) == CR.cr_path_in(ls, n) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %pd.path(l) : {Bool.or(Nat.is_eq(Cf.Leaf.path(l), n), Cf.listed(Cf.paths(t), n)) == Bool.or(Nat.is_eq(_, n), CR.cr_path_in(t, n)) : Bool}
      %pd.in(t, n) : {Bool.or(Nat.is_eq(Cf.Leaf.path(l), n), Cf.listed(Cf.paths(t), n)) == Bool.or(Nat.is_eq(Cf.Leaf.path(l), n), _) : Bool}
      {==}

def Config.distinct_exact(ls):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %pd.path(l) : {Bool.and(Bool.not(Cf.listed(Cf.paths(t), Cf.Leaf.path(l))), Cf.distinct(t)) == Bool.and(Bool.not(CR.cr_path_in(t, _)), CR.cr_distinct(t)) : Bool}
      %pd.in(t, Cf.Leaf.path(l)) : {Bool.and(Bool.not(Cf.listed(Cf.paths(t), Cf.Leaf.path(l))), Cf.distinct(t)) == Bool.and(Bool.not(_), CR.cr_distinct(t)) : Bool}
      %Config.distinct_exact(t) : {Bool.and(Bool.not(Cf.listed(Cf.paths(t), Cf.Leaf.path(l))), Cf.distinct(t)) == Bool.and(Bool.not(Cf.listed(Cf.paths(t), Cf.Leaf.path(l))), _) : Bool}
      {==}
