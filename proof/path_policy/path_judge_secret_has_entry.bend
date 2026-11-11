# eukhe: the proof of LAW path_judge_secret_has_entry
#
# PROOF: a loop never makes or unmakes a secret (phe.demote_secret_eq), and
# the class picked is a secret exactly when the model's secret test holds
# (pp.class_of_secret); so a Secret judgment has a secret entry at or above
# the path, which splits the entries (pin.find: se1 ++ s :: se2, the path
# k ++ s).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_inside_needs_root.bend as PPathInsideNeedsRoot

# a loop never makes or unmakes a secret
def phe.demote_secret_eq(c: Pp.Cls, l: Bool) -> {Pp.Cls.secret(Pp.demote(c, l)) == Pp.Cls.secret(c) : Bool}:
  match c:
    case Pp.Inside{}:
      match l:
        case True{}:
          {==}
        case False{}:
          {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def PathPolicy.path_judge_secret_has_entry(ro, ru, se, at, l, sec):
  +c = Pp.class_of(Pp.Pol{ro, ru, se}, at)
  +h1 = Equal.cong(Pp.Cls, Bool, x => Pp.Cls.secret(x), Pp.demote(c, l), Pp.Secret{}, sec)
  +h2 = Equal.trans(Bool, Pp.Cls.secret(c), Pp.Cls.secret(Pp.demote(c, l)), True{}, Equal.sym(Bool, Pp.Cls.secret(Pp.demote(c, l)), Pp.Cls.secret(c), phe.demote_secret_eq(c, l)), h1)
  +hu = Equal.trans(Bool, Pp.any_under(se, at), Pp.Cls.secret(c), True{}, Equal.sym(Bool, Pp.Cls.secret(c), Pp.any_under(se, at), LA.pp.class_of_secret(ro, ru, se, at)), h2)
  PPathInsideNeedsRoot.pin.find(se, at)(hu)
