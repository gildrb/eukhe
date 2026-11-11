# eukhe: the proof of LAW goal_text_escape_splits
#
# PROOF: induction on the first part: each char is escaped in front of the escape of the rest (gte.lt).

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def ges.lt(amp: Bool, lt: Bool, gt: Bool, -c: Char, -x: String, -y: String) -> {Gt.escape.lt(amp, lt, gt, c, String.append(x, y)) == String.append(Gt.escape.lt(amp, lt, gt, c, x), y) : String}:
  match amp:
    case True{}:
      {==}
    case False{}:
      match lt:
        case True{}:
          {==}
        case False{}:
          match gt:
            case True{}:
              {==}
            case False{}:
              {==}

def GoalText.goal_text_escape_splits(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(String, Gt.escape(String.append(t, b)), String.append(Gt.escape(t), Gt.escape(b)), GoalText.goal_text_escape_splits(t, b)) : {Gt.escape.lt(Char.is_eq(c, '&'), Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, _) == String.append(Gt.escape(SCon{c, t}), Gt.escape(b)) : String}
      ges.lt(Char.is_eq(c, '&'), Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, Gt.escape(t), Gt.escape(b))
