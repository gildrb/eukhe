# eukhe: the proof of LAW gate_terms_exact
#
# PROOF: each test is its spec: split the class (ppg.secret, ppg.guarded),
# the answer (ppg.yes) and, by induction, the history (ppg.any_yes).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./gate_runs_exact.bend as PGateRunsExact

def ppg.secret(c: Pp.Cls) -> {Pp.Cls.secret(c) == PathPolicyGate.pp_cls_secret(c) : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def ppg.guarded(c: Pp.Cls) -> {Pp.Cls.guarded(c) == PathPolicyGate.pp_cls_guarded(c) : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def ppg.any_yes(es: List<&2, Pp.Put>) -> {Pp.any_yes(es) == Bool.not(PathPolicy.pp_no_yes(es)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Pp.Put{s, v, a}:
          match a:
            case Pp.Yes{}:
              {==}
            case Pp.No{}:
              ppg.any_yes(rest)
            case Pp.Gone{}:
              ppg.any_yes(rest)

def ppg.terms(+c: Pp.Cls, +ans: Pp.Ans, +es: List<&2, Pp.Put>) -> {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [PathPolicyGate.pp_cls_secret(c), PathPolicyGate.pp_cls_guarded(c), PathPolicyGate.pp_yes(ans), Bool.not(PathPolicy.pp_no_yes(es))] : List<&2, Bool>}:
  %ppg.secret(c) : {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [_, PathPolicyGate.pp_cls_guarded(c), PathPolicyGate.pp_yes(ans), Bool.not(PathPolicy.pp_no_yes(es))] : List<&2, Bool>}
  %ppg.guarded(c) : {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [Pp.Cls.secret(c), _, PathPolicyGate.pp_yes(ans), Bool.not(PathPolicy.pp_no_yes(es))] : List<&2, Bool>}
  %PGateRunsExact.ppg.yes(ans) : {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [Pp.Cls.secret(c), Pp.Cls.guarded(c), _, Bool.not(PathPolicy.pp_no_yes(es))] : List<&2, Bool>}
  %ppg.any_yes(es) : {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), _] : List<&2, Bool>}
  {==}

def PathPolicyGate.gate_terms_exact(c, ans, es):
  ppg.terms(c, ans, es)
