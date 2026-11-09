# eukhe: the proof of LAW child_new_work_is_progress

import Base
import ../../bend/child.bend as Ch
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/child.bend as LChild
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# b is not a: a test that sees b at least 1 above a sees them differ
def pp.ne.at(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == c : Bool}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      LLogicLogic.pc.lt_ne({Bool.not(True{}) == True{} : Bool}, a, b, lt, e)
    case False{}:
      {==}

def pp.ne(+a: Nat, +b: Nat, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}:
  pp.ne.at(Nat.is_eq(a, b), a, b, {==}, lt)

# a poll that reads more work than the watch holds is progress
def pp.news(+tok: Maybe<&2, Nat>, +a: Nat, +b: Nat, held: {tok == Some{a} : Maybe<&2, Nat>}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Ch.moved(tok, Some{b}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, tok, Some{a}, held) : {Ch.moved(_, Some{b}) == True{} : Bool}
  pp.ne(a, b, lt)

def pp.new_work_moves(+s: Nat, +f: Nat, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +e: Nat, +seen: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, seen) == False{} : Bool}, i: Pr.In(x, seg), held: {tok == Some{Pr.work(seen)} : Maybe<&2, Nat>}) -> {Ch.look(Ch.Cfg{s, f}, Ch.W{tok, l, n}, e, Ch.Busy{Some{Pr.work(List.append(&2, Nat, seen, seg))}}) == Ch.Watch{Ch.W{Some{Pr.work(List.append(&2, Nat, seen, seg))}, s, f}} : Ch.Next}:
  +b = Pr.work(List.append(&2, Nat, seen, seg))
  LChild.pc.progress(s, f, tok, l, n, e, b, pp.news(tok, Pr.work(seen), b, held, LA.pp.new_work(seen, seg, x, fresh, i)))

def Progress.child_new_work_is_progress(s, f, tok, l, n, e, seen, seg, x, fresh, news, held):
  pp.new_work_moves(s, f, tok, l, n, e, seen, seg, x, fresh, news, held)
