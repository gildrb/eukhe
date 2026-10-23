# eukhe: the proof of LAW cow_plan

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws

# The plan of one path, for any three equalities of its contents: the
# copy-on-write rule, and the merge it carries out.

def px.plan(calm: Bool, still: Bool, same: Bool, c: Maybe<&2, Nat>) -> {Sb.plan.at(calm, still, same, c) == Laws.CowPlan.go(calm, still, same, c) : Sb.Plan}:
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

def Laws.cow_plan(p, b, c):
  px.plan(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c)
