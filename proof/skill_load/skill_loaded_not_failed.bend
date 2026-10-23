# eukhe: the proof of LAW skill_loaded_not_failed

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ../base.bend as L

# a loaded path is the path of a candidate
def ppr.loaded_sub(cs: List<&2, Sk.Cand>, +q: Nat) -> {Sk.listed(Sk.loaded(cs), q) == True{} : Bool} -> {Sk.listed(Sk.paths(cs), q) == True{} : Bool}:
  match cs:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              h => L.ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.loaded(rest), q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q), h)
            case Sk.Unreadable{}:
              h => L.ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))
            case Sk.Malformed{}:
              h => L.ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))
            case Sk.Incomplete{}:
              h => L.ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))

# a reported path is the path of a candidate
def ppr.named_sub(cs: List<&2, Sk.Cand>, +q: Nat) -> {Sk.listed(Sk.named(Sk.diags(cs)), q) == True{} : Bool} -> {Sk.listed(Sk.paths(cs), q) == True{} : Bool}:
  match cs:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              h => L.ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q)(h))
            case Sk.Unreadable{}:
              h => L.ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)
            case Sk.Malformed{}:
              h => L.ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)
            case Sk.Incomplete{}:
              h => L.ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)

# a list of paths of rest does not name q when the paths of rest do not
def ppr.not_in(b: Bool, +ns: List<&2, Nat>, +rest: List<&2, Sk.Cand>, +q: Nat, eb: {Sk.listed(ns, q) == b : Bool}, sub: {Sk.listed(ns, q) == True{} : Bool} -> {Sk.listed(Sk.paths(rest), q) == True{} : Bool}, out: {Sk.listed(Sk.paths(rest), q) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      L.ppr.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Sk.listed(Sk.paths(rest), q), False{}, Equal.sym(Bool, Sk.listed(Sk.paths(rest), q), True{}, sub(eb)), out))
    case False{}:
      {==}

# a good candidate of path p, c saying whether p is n
def ppr.good_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Sk.Cand>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Sk.listed(Sk.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}) -> {Bool.and(Bool.or(c, Sk.listed(Sk.loaded(rest), n)), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}:
  match c:
    case True{}:
      %L.ppr.nat_eq_true(p, n, ec) : {Sk.listed(Sk.named(Sk.diags(rest)), _) == False{} : Bool}
      ppr.not_in(Sk.listed(Sk.named(Sk.diags(rest)), p), Sk.named(Sk.diags(rest)), rest, p, {==}, ppr.named_sub(rest, p), dp)
    case False{}:
      ih

# a candidate of path p that does not load, c saying whether p is n
def ppr.bad_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Sk.Cand>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Sk.listed(Sk.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}) -> {Bool.and(Sk.listed(Sk.loaded(rest), n), Bool.or(c, Sk.listed(Sk.named(Sk.diags(rest)), n))) == False{} : Bool}:
  match c:
    case True{}:
      +eL = ppr.not_in(Sk.listed(Sk.loaded(rest), p), Sk.loaded(rest), rest, p, {==}, ppr.loaded_sub(rest, p), dp)
      %L.ppr.nat_eq_true(p, n, ec) : {Bool.and(Sk.listed(Sk.loaded(rest), _), True{}) == False{} : Bool}
      %Equal.sym(Bool, Sk.listed(Sk.loaded(rest), p), False{}, eL) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case False{}:
      ih

# LAW skill_loaded_not_failed: when no two candidates share a path, no
# path is both loaded and named by a diagnostic
def ppr.skill_loaded_not_failed(cs: List<&2, Sk.Cand>, +n: Nat, +d: {Sk.distinct(cs) == True{} : Bool}) -> {Bool.and(Sk.listed(Sk.loaded(cs), n), Sk.listed(Sk.named(Sk.diags(cs)), n)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = L.ppr.not_t(Sk.listed(Sk.paths(rest), p), L.ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.good_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, L.ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Unreadable{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = L.ppr.not_t(Sk.listed(Sk.paths(rest), p), L.ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, L.ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Malformed{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = L.ppr.not_t(Sk.listed(Sk.paths(rest), p), L.ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, L.ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Incomplete{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = L.ppr.not_t(Sk.listed(Sk.paths(rest), p), L.ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, L.ppr.and_r(nd, Sk.distinct(rest), d)))

def SkillLoad.skill_loaded_not_failed(cs, n, d):
  ppr.skill_loaded_not_failed(cs, n, d)
