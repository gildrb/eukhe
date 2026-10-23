# eukhe: the proof of LAW leaf_applied_or_reported

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/bool.bend as LBool
import ../base/nat.bend as LNat

# Leaves
# ------

# the leaf x applies or is reported
def pcf.leaf_head(+x: Cf.Leaf, +rest: List<&2, Cf.Leaf>) -> {Bool.or(Cf.listed(Cf.applied(x <> rest), Cf.Leaf.path(x)), Cf.listed(Cf.reported(x <> rest), Cf.Leaf.path(x))) == True{} : Bool}:
  match x:
    case Cf.Leaf{+p, o}:
      match o:
        case Cf.Good{}:
          +a = Cf.listed(Cf.applied(rest), p)
          LBool.ppr.or_l(Bool.or(Nat.is_eq(p, p), a), Cf.listed(Cf.reported(rest), p), LBool.ppr.or_l(Nat.is_eq(p, p), a, LNat.ppr.nat_eq_refl(p)))
        case Cf.BadType{}:
          +b = Cf.listed(Cf.reported(rest), p)
          LBool.ppr.or_r(Cf.listed(Cf.applied(rest), p), Bool.or(Nat.is_eq(p, p), b), LBool.ppr.or_l(Nat.is_eq(p, p), b, LNat.ppr.nat_eq_refl(p)))
        case Cf.Undeclared{}:
          +b = Cf.listed(Cf.reported(rest), p)
          LBool.ppr.or_r(Cf.listed(Cf.applied(rest), p), Bool.or(Nat.is_eq(p, p), b), LBool.ppr.or_l(Nat.is_eq(p, p), b, LNat.ppr.nat_eq_refl(p)))

# a path that applies or is reported in rest stays so with x before rest
def pcf.leaf_cons(+x: Cf.Leaf, +rest: List<&2, Cf.Leaf>, +n: Nat, h: {Bool.or(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == True{} : Bool}) -> {Bool.or(Cf.listed(Cf.applied(x <> rest), n), Cf.listed(Cf.reported(x <> rest), n)) == True{} : Bool}:
  match x:
    case Cf.Leaf{+p, o}:
      match o:
        case Cf.Good{}:
          LBool.ppr.or_in_l(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)
        case Cf.BadType{}:
          LBool.ppr.or_in_r(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)
        case Cf.Undeclared{}:
          LBool.ppr.or_in_r(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)

# LAW leaf_applied_or_reported
def pcf.leaf_applied_or_reported(ls: List<&2, Cf.Leaf>, +l: Cf.Leaf, i: Cf.In(l, ls)) -> {Bool.or(Cf.listed(Cf.applied(ls), Cf.Leaf.path(l)), Cf.listed(Cf.reported(ls), Cf.Leaf.path(l))) == True{} : Bool}:
  match ls:
    case Nil{}:
      match i:
    case +x <> +rest:
      match i:
        case Inl{eq}:
          %Equal.sym(Cf.Leaf, l, x, eq) : {Bool.or(Cf.listed(Cf.applied(x <> rest), Cf.Leaf.path(_)), Cf.listed(Cf.reported(x <> rest), Cf.Leaf.path(_))) == True{} : Bool}
          pcf.leaf_head(x, rest)
        case Inr{it}:
          pcf.leaf_cons(x, rest, Cf.Leaf.path(l), pcf.leaf_applied_or_reported(rest, l, it))

def Config.leaf_applied_or_reported(ls, l, i):
  pcf.leaf_applied_or_reported(ls, l, i)
