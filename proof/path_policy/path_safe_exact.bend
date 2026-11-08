# eukhe: the proof of LAW path_safe_exact
#
# PROOF: safe and the spec class read the same three tests: a secret
# covers the path (LA.pp.any_under_spec), it is protected (pc.prot_eq),
# a root holds it (pc.has_root, LA.pp.any_under_spec); then a finite check
# over the three and the loop (psf.pick).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_judge_class_exact.bend as PPathJudgeClassExact

def psf.pick(l: Bool, s: Bool, p: Bool, i: Bool) -> {Bool.and(Bool.not(l), Pp.inside_ok(s, p, i)) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_cls_pick(s, p, Bool.and(i, Bool.not(l)))) : Bool}:
  match l:
    case True{}:
      match s:
        case True{}:
          match p:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match p:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match s:
        case True{}:
          match p:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match p:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}

def psf.safe(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool) -> {Pp.safe(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_class(ro, ru, se, at, l)) : Bool}:
  %LA.pp.any_under_spec(se, at) : {Pp.safe(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_cls_pick(_, Bool.or(PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below_root(ro, at)), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))), Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l)))) : Bool}
  %PPathJudgeClassExact.pc.prot_eq(ro, ru, se, at) : {Pp.safe(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_cls_pick(Pp.any_under(se, at), _, Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l)))) : Bool}
  %LA.pp.any_under_spec(ro, at) : {Pp.safe(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_cls_pick(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Bool.and(_, Bool.not(l)))) : Bool}
  %PPathJudgeClassExact.pc.has_root(ro, at) : {Pp.safe(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_cls_is_inside(PathPolicy.pp_cls_pick(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Bool.and(_, Bool.not(l)))) : Bool}
  psf.pick(l, Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)))

def PathPolicy.path_safe_exact(ro, ru, se, at, l):
  psf.safe(ro, ru, se, at, l)
