# eukhe: the proof of LAW shell_script_runs_all
#
# PROOF: by induction on the script: a step that writes no own path runs
# and the rest runs as before; a step that writes one contradicts the
# premise.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ../base/staging.bend as LStg

def ssr.go(ss: List<&2, Tl.Planned>, free: {Shell.sh_none_own(ss) == True{} : Bool}) -> {Tl.script(ss) == Tl.Did{Shell.sh_steps(ss), Tl.AllRan{}} : Tl.Did}:
  match ss:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Tl.Planned{+i, +e, m}:
          match m:
            case True{}:
              LStg.stg.absurdF({Tl.script(Tl.Planned{i, e, True{}} <> rest) == Tl.Did{Shell.sh_steps(Tl.Planned{i, e, True{}} <> rest), Tl.AllRan{}} : Tl.Did}, free)
            case False{}:
              %Equal.sym(Tl.Did, Tl.script(rest), Tl.Did{Shell.sh_steps(rest), Tl.AllRan{}}, ssr.go(rest, free)) : {Tl.did.add(Tl.Step{i, e}, _) == Tl.Did{Tl.Step{i, e} <> Shell.sh_steps(rest), Tl.AllRan{}} : Tl.Did}
              {==}

def Shell.shell_script_runs_all(ss, free):
  ssr.go(ss, free)
