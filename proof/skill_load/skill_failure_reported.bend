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

def sfr.val(x: Sk.Cand, m: Maybe<&2, Sk.Cand>) -> Sk.Cand:
  match m:
    case None{}:
      x
    case Some{y}:
      y

def sfr.If(m: Maybe<&2, Sk.Cand>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      G

def sfr.none(-G: Type, -c: Sk.Cand, e: {None{} == Some{c} : Maybe<&2, Sk.Cand>}) -> G:
  %e : sfr.If(_, G)
  Unit{}

def sfr.inj(+x: Sk.Cand, -c: Sk.Cand, e: {Some{x} == Some{c} : Maybe<&2, Sk.Cand>}) -> {x == c : Sk.Cand}:
  Equal.cong(Maybe<&2, Sk.Cand>, Sk.Cand, m => sfr.val(x, m), Some{x}, Some{c}, e)

# LAW skill_failure_reported: the path of the candidate at every index is
# on the loaded list or named by a diagnostic
def ppr.skill_failure_reported(cs: List<&2, Sk.Cand>, i: Nat, +c: Sk.Cand, at: {List.get(&2, Sk.Cand, cs, i) == Some{c} : Maybe<&2, Sk.Cand>}) -> {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}:
  match cs i:
    case Nil{} _:
      sfr.none({Bool.or(Sk.listed(Sk.loaded(Nil{}), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(Nil{})), Sk.Cand.path(c))) == True{} : Bool}, c, at)
    case +x <> +rest 0n:
      %sfr.inj(x, c, at) : {Bool.or(Sk.listed(Sk.loaded(x <> rest), Sk.Cand.path(_)), Sk.listed(Sk.named(Sk.diags(x <> rest)), Sk.Cand.path(_))) == True{} : Bool}
      ppr.skill_head(x, rest)
    case +x <> +rest 1n+j:
      ppr.skill_cons(x, rest, Sk.Cand.path(c), ppr.skill_failure_reported(rest, j, c, at))

def SkillLoad.skill_failure_reported(cs, i, c, at):
  ppr.skill_failure_reported(cs, i, c, at)
