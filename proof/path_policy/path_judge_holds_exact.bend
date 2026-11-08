# eukhe: the proof of LAW path_judge_holds_exact

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA

def PathPolicy.path_judge_holds_exact(ro, ru, se, at, l):
  %LA.pp.any_under_spec(se, at) : {Bool.or(Pp.any_under(se, at), Pp.any_ancestor(se, at)) == Bool.or(_, PathPolicy.pp_above_any(se, at)) : Bool}
  %LA.pp.any_ancestor_spec(se, at) : {Bool.or(Pp.any_under(se, at), Pp.any_ancestor(se, at)) == Bool.or(Pp.any_under(se, at), _) : Bool}
  {==}
