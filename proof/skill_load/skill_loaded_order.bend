# eukhe: the proof of LAW skill_loaded_order

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad

# by induction on xs: a good head keeps its path in front
def slo.order(xs: List<&2, Sk.Cand>, -ys: List<&2, Sk.Cand>) -> {Sk.loaded(List.append(&2, Sk.Cand, xs, ys)) == List.append(&2, Nat, Sk.loaded(xs), Sk.loaded(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Sk.Cand{p, o}:
          match o:
            case Sk.Good{}:
              %slo.order(rest, ys) : {p <> Sk.loaded(List.append(&2, Sk.Cand, rest, ys)) == p <> _ : List<&2, Nat>}
              {==}
            case Sk.Unreadable{}:
              slo.order(rest, ys)
            case Sk.Malformed{}:
              slo.order(rest, ys)
            case Sk.Incomplete{}:
              slo.order(rest, ys)

def SkillLoad.skill_loaded_order(xs, ys):
  slo.order(xs, ys)
