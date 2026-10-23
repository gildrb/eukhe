# eukhe: the proof of LAW skill_failure_reported

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ../base/bool.bend as LBool
import ../base/nat.bend as LNat

# the candidate x is loaded or reported
def ppr.skill_head(+x: Sk.Cand, +rest: List<&2, Sk.Cand>) -> {Bool.or(Sk.listed(Sk.loaded(x <> rest), Sk.Cand.path(x)), Sk.listed(Sk.named(Sk.diags(x <> rest)), Sk.Cand.path(x))) == True{} : Bool}:
  match x:
    case Sk.Cand{+p, o}:
      match o:
        case Sk.Good{}:
          +a = Sk.listed(Sk.loaded(rest), p)
          LBool.ppr.or_l(Bool.or(Nat.is_eq(p, p), a), Sk.listed(Sk.named(Sk.diags(rest)), p), LBool.ppr.or_l(Nat.is_eq(p, p), a, LNat.ppr.nat_eq_refl(p)))
        case Sk.Unreadable{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          LBool.ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), LBool.ppr.or_l(Nat.is_eq(p, p), b, LNat.ppr.nat_eq_refl(p)))
        case Sk.Malformed{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          LBool.ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), LBool.ppr.or_l(Nat.is_eq(p, p), b, LNat.ppr.nat_eq_refl(p)))
        case Sk.Incomplete{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          LBool.ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), LBool.ppr.or_l(Nat.is_eq(p, p), b, LNat.ppr.nat_eq_refl(p)))

# a path loaded or reported in rest stays so with x before rest
def ppr.skill_cons(+x: Sk.Cand, +rest: List<&2, Sk.Cand>, +n: Nat, h: {Bool.or(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == True{} : Bool}) -> {Bool.or(Sk.listed(Sk.loaded(x <> rest), n), Sk.listed(Sk.named(Sk.diags(x <> rest)), n)) == True{} : Bool}:
  match x:
    case Sk.Cand{+p, o}:
      match o:
        case Sk.Good{}:
          LBool.ppr.or_in_l(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Unreadable{}:
          LBool.ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Malformed{}:
          LBool.ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Incomplete{}:
          LBool.ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)

# LAW skill_failure_reported: the path of every candidate file is on the
# loaded list or named by a diagnostic
def ppr.skill_failure_reported(cs: List<&2, Sk.Cand>, +c: Sk.Cand, i: Sk.In(c, cs)) -> {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}:
  match cs:
    case Nil{}:
      match i:
    case +x <> +rest:
      match i:
        case Inl{eq}:
          %Equal.sym(Sk.Cand, c, x, eq) : {Bool.or(Sk.listed(Sk.loaded(x <> rest), Sk.Cand.path(_)), Sk.listed(Sk.named(Sk.diags(x <> rest)), Sk.Cand.path(_))) == True{} : Bool}
          ppr.skill_head(x, rest)
        case Inr{it}:
          ppr.skill_cons(x, rest, Sk.Cand.path(c), ppr.skill_failure_reported(rest, c, it))

def SkillLoad.skill_failure_reported(cs, c, i):
  ppr.skill_failure_reported(cs, c, i)
