# eukhe: the proof of LAW goal_text_left_canonical
#
# PROOF: the tokens left are `0` or a text passed through canon, and canon
# answers `0` or a text whose first char is no `0` (gtc.canon, by
# induction: canon drops a leading `0` and stops at the first other char).
# The premises on the digits are not needed.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ../../laws/base.bend as LawsBase

def gtc.at(z: Bool, +c: Char, t: String, e: {Char.is_eq(c, '0') == z : Bool}, ih: {GoalText.gt_canonical(Gt.canon(t)) == True{} : Bool}) -> {GoalText.gt_canonical(Gt.canon.fin(Gt.canon.at(z, c, t, Gt.canon.go(t)))) == True{} : Bool}:
  match z:
    case True{}:
      ih
    case False{}:
      match t:
        case SNil{}:
          {==}
        case SCon{d, r}:
          %Equal.sym(Bool, Char.is_eq(c, '0'), False{}, e) : {Bool.not(_) == True{} : Bool}
          {==}

def gtc.canon(s: String) -> {GoalText.gt_canonical(Gt.canon(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      gtc.at(Char.is_eq(c, '0'), c, t, {==}, gtc.canon(t))

def gtc.of(z: Bool, +b: String, +u: String) -> {GoalText.gt_canonical(Gt.left.of(z, b, u)) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      gtc.canon(String.reverse(Gt.sub.go(String.reverse(b), String.reverse(u), 0n)))

def GoalText.goal_text_left_canonical(ds, es, hd, he):
  +b = Gt.canon(LawsBase.wire_digit_chars(ds, ""))
  +u = Gt.canon(LawsBase.wire_digit_chars(es, ""))
  gtc.of(Gt.below(b, u), b, u)
