# eukhe: the proof of LAW gate_runs_exact
#
# PROOF: the model's effects are pp_effs (gate_effs_exact); its auto
# test is pp_auto_holds item by item (ppg.allows: grantable is the bound
# 7, Tl.elem is pp_has_name, the conjuncts reordered); its answer test is
# pp_yes (ppg.yes).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./gate_effs_exact.bend as PGateEffsExact

def ppg.elem(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == PathPolicy.pp_has_name(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %ppg.elem(rest, x) : {Tl.elem(y <> rest, x) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def ppg.and3(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, c), b) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      {==}

def ppg.allows(+auto: List<&2, Nat>, es: List<&2, Nat>) -> {Pp.allows(auto, es) == PathPolicyGate.pp_auto_holds(auto, es) : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %ppg.allows(auto, rest) : {Pp.allows(auto, e <> rest) == Bool.and(Bool.and(Nat.is_lt(e, 7n), PathPolicy.pp_has_name(auto, e)), _) : Bool}
      %ppg.elem(auto, e) : {Pp.allows(auto, e <> rest) == Bool.and(Bool.and(Nat.is_lt(e, 7n), _), Pp.allows(auto, rest)) : Bool}
      ppg.and3(Nat.is_lt(e, 7n), Pp.allows(auto, rest), Tl.elem(auto, e))

def ppg.yes(a: Pp.Ans) -> {Pp.Ans.yes(a) == PathPolicyGate.pp_yes(a) : Bool}:
  match a:
    case Pp.Yes{}:
      {==}
    case Pp.No{}:
      {==}
    case Pp.Gone{}:
      {==}

def ppg.runs(+c: Pp.Cls, +a: Pp.Acc, +auto: List<&2, Nat>, +ans: Pp.Ans) -> {Pp.runs(c, a, auto, ans) == Bool.or(PathPolicyGate.pp_auto_holds(auto, PathPolicyGate.pp_effs(c, a)), PathPolicyGate.pp_yes(ans)) : Bool}:
  %PathPolicyGate.gate_effs_exact(c, a) : {Pp.runs(c, a, auto, ans) == Bool.or(PathPolicyGate.pp_auto_holds(auto, _), PathPolicyGate.pp_yes(ans)) : Bool}
  %ppg.allows(auto, Pp.effs(c, a)) : {Pp.runs(c, a, auto, ans) == Bool.or(_, PathPolicyGate.pp_yes(ans)) : Bool}
  %ppg.yes(ans) : {Pp.runs(c, a, auto, ans) == Bool.or(Pp.allows(auto, Pp.effs(c, a)), _) : Bool}
  {==}

def PathPolicyGate.gate_runs_exact(c, a, auto, ans):
  ppg.runs(c, a, auto, ans)
