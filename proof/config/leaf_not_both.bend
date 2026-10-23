# eukhe: the proof of LAW leaf_not_both

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat

# an applied path is the path of a leaf
def pcf.applied_sub(ls: List<&2, Cf.Leaf>, +q: Nat) -> {Cf.listed(Cf.applied(ls), q) == True{} : Bool} -> {Cf.listed(Cf.paths(ls), q) == True{} : Bool}:
  match ls:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              h => LBool.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.applied(rest), q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q), h)
            case Cf.BadType{}:
              h => LBool.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q)(h))
            case Cf.Undeclared{}:
              h => LBool.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q)(h))

# a reported path is the path of a leaf
def pcf.reported_sub(ls: List<&2, Cf.Leaf>, +q: Nat) -> {Cf.listed(Cf.reported(ls), q) == True{} : Bool} -> {Cf.listed(Cf.paths(ls), q) == True{} : Bool}:
  match ls:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              h => LBool.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q)(h))
            case Cf.BadType{}:
              h => LBool.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.reported(rest), q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q), h)
            case Cf.Undeclared{}:
              h => LBool.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.reported(rest), q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q), h)

# a list of paths of rest does not name q when the paths of rest do not
def pcf.not_in(b: Bool, +ns: List<&2, Nat>, +rest: List<&2, Cf.Leaf>, +q: Nat, eb: {Cf.listed(ns, q) == b : Bool}, sub: {Cf.listed(ns, q) == True{} : Bool} -> {Cf.listed(Cf.paths(rest), q) == True{} : Bool}, out: {Cf.listed(Cf.paths(rest), q) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.ppr.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Cf.listed(Cf.paths(rest), q), False{}, Equal.sym(Bool, Cf.listed(Cf.paths(rest), q), True{}, sub(eb)), out))
    case False{}:
      {==}

# a good leaf of path p, c saying whether p is n
def pcf.good_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Cf.Leaf>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Cf.listed(Cf.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}) -> {Bool.and(Bool.or(c, Cf.listed(Cf.applied(rest), n)), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}:
  match c:
    case True{}:
      %LLogicNat.ppr.nat_eq_true(p, n, ec) : {Cf.listed(Cf.reported(rest), _) == False{} : Bool}
      pcf.not_in(Cf.listed(Cf.reported(rest), p), Cf.reported(rest), rest, p, {==}, pcf.reported_sub(rest, p), dp)
    case False{}:
      ih

# a leaf of path p that does not apply, c saying whether p is n
def pcf.bad_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Cf.Leaf>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Cf.listed(Cf.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}) -> {Bool.and(Cf.listed(Cf.applied(rest), n), Bool.or(c, Cf.listed(Cf.reported(rest), n))) == False{} : Bool}:
  match c:
    case True{}:
      +eL = pcf.not_in(Cf.listed(Cf.applied(rest), p), Cf.applied(rest), rest, p, {==}, pcf.applied_sub(rest, p), dp)
      %LLogicNat.ppr.nat_eq_true(p, n, ec) : {Bool.and(Cf.listed(Cf.applied(rest), _), True{}) == False{} : Bool}
      %Equal.sym(Bool, Cf.listed(Cf.applied(rest), p), False{}, eL) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case False{}:
      ih

# LAW leaf_not_both
def pcf.leaf_not_both(ls: List<&2, Cf.Leaf>, +n: Nat, +d: {Cf.distinct(ls) == True{} : Bool}) -> {Bool.and(Cf.listed(Cf.applied(ls), n), Cf.listed(Cf.reported(ls), n)) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = LLogicBool.ppr.not_t(Cf.listed(Cf.paths(rest), p), LLogicBool.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.good_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, LLogicBool.ppr.and_r(nd, Cf.distinct(rest), d)))
            case Cf.BadType{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = LLogicBool.ppr.not_t(Cf.listed(Cf.paths(rest), p), LLogicBool.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, LLogicBool.ppr.and_r(nd, Cf.distinct(rest), d)))
            case Cf.Undeclared{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = LLogicBool.ppr.not_t(Cf.listed(Cf.paths(rest), p), LLogicBool.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, LLogicBool.ppr.and_r(nd, Cf.distinct(rest), d)))

def Config.leaf_not_both(ls, n, d):
  pcf.leaf_not_both(ls, n, d)
