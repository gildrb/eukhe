# eukhe: the proof of LAW cow_plan_is_merge

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox

def px.plan_merge(calm: Bool, still: Bool, same: Bool, +p: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> {Sb.Plan.merge(Sb.plan.at(calm, still, same, c), p, c) == Sb.merge.at(Bool.not(calm), Bool.not(still), same, p, c) : Sb.One}:
  match calm:
    case True{}:
      {==}
    case False{}:
      match still:
        case True{}:
          match c:
            case None{}:
              {==}
            case Some{x}:
              {==}
        case False{}:
          match same:
            case True{}:
              {==}
            case False{}:
              {==}

def Sandbox.cow_plan_is_merge(p, b, c):
  px.plan_merge(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), p, c)
