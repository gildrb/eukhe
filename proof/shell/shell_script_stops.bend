# eukhe: the proof of LAW shell_script_stops
#
# PROOF: by induction on the steps before the refused one: each writes no
# own path, so it runs and the rest runs as before; the refused step stops
# the script there.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ../base/staging.bend as LStg

def sss.go(pre: List<&2, Tl.Planned>, +i: Nat, +e: List<&2, Nat>, +post: List<&2, Tl.Planned>, free: {Shell.sh_none_own(pre) == True{} : Bool}) -> {Tl.script(List.append(&2, Tl.Planned, pre, Tl.Planned{i, e, True{}} <> post)) == Tl.Did{Shell.sh_steps(pre), Tl.StoppedAt{i}} : Tl.Did}:
  match pre:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Tl.Planned{+j, +f, m}:
          match m:
            case True{}:
              LStg.stg.absurdF({Tl.script(List.append(&2, Tl.Planned, Tl.Planned{j, f, True{}} <> rest, Tl.Planned{i, e, True{}} <> post)) == Tl.Did{Shell.sh_steps(Tl.Planned{j, f, True{}} <> rest), Tl.StoppedAt{i}} : Tl.Did}, free)
            case False{}:
              %Equal.sym(Tl.Did, Tl.script(List.append(&2, Tl.Planned, rest, Tl.Planned{i, e, True{}} <> post)), Tl.Did{Shell.sh_steps(rest), Tl.StoppedAt{i}}, sss.go(rest, i, e, post, free)) : {Tl.did.add(Tl.Step{j, f}, _) == Tl.Did{Tl.Step{j, f} <> Shell.sh_steps(rest), Tl.StoppedAt{i}} : Tl.Did}
              {==}

def Shell.shell_script_stops(pre, i, e, post, free):
  sss.go(pre, i, e, post, free)
