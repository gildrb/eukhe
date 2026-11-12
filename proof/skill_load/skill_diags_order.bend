# eukhe: the proof of LAW skill_diags_order

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad

# by induction on xs: a failed head keeps its diagnostic in front
def sdo.order(xs: List<&2, Sk.Cand>, -ys: List<&2, Sk.Cand>) -> {Sk.diags(List.append(&2, Sk.Cand, xs, ys)) == List.append(&2, Sk.Diag, Sk.diags(xs), Sk.diags(ys)) : List<&2, Sk.Diag>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Sk.Cand{p, o}:
          match o:
            case Sk.Good{}:
              sdo.order(rest, ys)
            case Sk.Unreadable{}:
              %sdo.order(rest, ys) : {Sk.Diag{p, 0n} <> Sk.diags(List.append(&2, Sk.Cand, rest, ys)) == Sk.Diag{p, 0n} <> _ : List<&2, Sk.Diag>}
              {==}
            case Sk.Malformed{}:
              %sdo.order(rest, ys) : {Sk.Diag{p, 1n} <> Sk.diags(List.append(&2, Sk.Cand, rest, ys)) == Sk.Diag{p, 1n} <> _ : List<&2, Sk.Diag>}
              {==}
            case Sk.Incomplete{}:
              %sdo.order(rest, ys) : {Sk.Diag{p, 2n} <> Sk.diags(List.append(&2, Sk.Cand, rest, ys)) == Sk.Diag{p, 2n} <> _ : List<&2, Sk.Diag>}
              {==}

def SkillLoad.skill_diags_order(xs, ys):
  sdo.order(xs, ys)
