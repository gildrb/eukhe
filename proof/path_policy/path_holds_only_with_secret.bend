# eukhe: the proof of LAW path_holds_only_with_secret
#
# PROOF: the judgment's holds is the secret test or the ancestor test of
# the secret entries (pho.split on the secret test). Secret test: an entry
# s is at or above at (pin.find: at is k ++ s), and at itself is the common
# location (k ++ s, [] ++ at). Ancestor test: at is strictly above an entry
# s (pho.afind: s is j ++ at, from the entry's under test by pin.usplit),
# and s is the common location ([] ++ s, j ++ at).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/lemmas.bend as LAE
import ./path_inside_needs_root.bend as PPathInsideNeedsRoot

# the law's witnesses
def pho.W(se: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> Type:
  &se1: List<&2, List<&2, Nat>> -> &s: List<&2, Nat> -> &se2: List<&2, List<&2, Nat>> -> &k1: List<&2, Nat> -> &k2: List<&2, Nat> -> ({se == List.append(&2, List<&2, Nat>, se1, s <> se2) : List<&2, List<&2, Nat>>} & {List.append(&2, Nat, k1, s) == List.append(&2, Nat, k2, at) : List<&2, Nat>})

# an entry s of se is under at: s is j ++ at
def pho.A(se: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> Type:
  &se1: List<&2, List<&2, Nat>> -> &s: List<&2, Nat> -> &se2: List<&2, List<&2, Nat>> -> &j: List<&2, Nat> -> ({se == List.append(&2, List<&2, Nat>, se1, s <> se2) : List<&2, List<&2, Nat>>} & {s == List.append(&2, Nat, j, at) : List<&2, Nat>})

def pho.a_here(+p: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, s: PPathInsideNeedsRoot.pin.Suf(at, p)) -> pho.A(p <> rest, at):
  match s:
    case (+j, e):
      (Nil{}, (p, (rest, (j, ({==}, e)))))

def pho.a_cons(+p: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, g: pho.A(rest, at)) -> pho.A(p <> rest, at):
  match g:
    case (+se1, g1):
      match g1:
        case (+s, g2):
          match g2:
            case (+se2, g3):
              match g3:
                case (+j, g4):
                  (e1, e2) = g4
                  (p <> se1, (s, (se2, (j, (Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => p <> z, rest, List.append(&2, List<&2, Nat>, se1, s <> se2), e1), e2)))))

def pho.a_at(b: Bool, +p: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, eb: {Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))) == b : Bool}, h: {Bool.or(b, Pp.any_ancestor(rest, at)) == True{} : Bool}, ih: {Pp.any_ancestor(rest, at) == True{} : Bool} -> pho.A(rest, at)) -> pho.A(p <> rest, at):
  match b:
    case True{}:
      pho.a_here(p, rest, at, PPathInsideNeedsRoot.pin.usplit(at, p)(LAE.pp.and_l(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p)), eb)))
    case False{}:
      pho.a_cons(p, rest, at, ih(h))

# the ancestor test names an entry under at
def pho.afind(se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(se, at) == True{} : Bool} -> pho.A(se, at):
  match se:
    case Nil{}:
      h => LA.pp.absurdF(pho.A(Nil{}, at), h)
    case +p <> +rest:
      h => pho.a_at(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), p, rest, at, {==}, h, pho.afind(rest, at))

# an entry at or above at: at is the common location
def pho.from_under(-se: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, g: PPathInsideNeedsRoot.pin.Goal(se, at)) -> pho.W(se, at):
  match g:
    case (+se1, g1):
      match g1:
        case (+s, g2):
          match g2:
            case (+se2, g3):
              match g3:
                case (+k, g4):
                  (e1, e2) = g4
                  (se1, (s, (se2, (k, (Nil{}, (e1, Equal.sym(List<&2, Nat>, at, List.append(&2, Nat, k, s), e2)))))))

# an entry under at: the entry is the common location
def pho.from_anc(-se: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, g: pho.A(se, at)) -> pho.W(se, at):
  match g:
    case (+se1, g1):
      match g1:
        case (+s, g2):
          match g2:
            case (+se2, g3):
              match g3:
                case (+j, g4):
                  (e1, e2) = g4
                  (se1, (s, (se2, (Nil{}, (j, (e1, e2))))))

# by the secret test u
def pho.split(u: Bool, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, eu: {Pp.any_under(se, at) == u : Bool}, h: {Bool.or(u, Pp.any_ancestor(se, at)) == True{} : Bool}) -> pho.W(se, at):
  match u:
    case True{}:
      pho.from_under(se, at, PPathInsideNeedsRoot.pin.find(se, at)(eu))
    case False{}:
      pho.from_anc(se, at, pho.afind(se, at)(h))

def PathPolicy.path_holds_only_with_secret(ro, ru, se, at, l, holds):
  pho.split(Pp.any_under(se, at), se, at, {==}, holds)
