# eukhe: the proof of LAW child_new_work_is_progress

import Base
import ../../bend/child.bend as Ch
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/child.bend as LChild
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

# b is not a: a test that sees b at least 1 above a sees them differ
def pp.ne.at(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == c : Bool}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      LNatIsLe.pc.lt_ne({Bool.not(True{}) == True{} : Bool}, a, b, lt, e)
    case False{}:
      {==}

def pp.ne(+a: Nat, +b: Nat, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}:
  pp.ne.at(Nat.is_eq(a, b), a, b, {==}, lt)

# a poll that reads more work than the watch holds is progress
def pp.news(+w: Ch.W, +a: Nat, +b: Nat, tok: {Ch.W.tok(w) == Some{a} : Maybe<&2, Nat>}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Ch.moved(Ch.W.tok(w), Some{b}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, Ch.W.tok(w), Some{a}, tok) : {Ch.moved(_, Some{b}) == True{} : Bool}
  pp.ne(a, b, lt)

def pp.new_work_moves(+cfg: Ch.Cfg, +w: Ch.W, +e: Nat, +seen: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, seen) == False{} : Bool}, i: Pr.In(x, seg), tok: {Ch.W.tok(w) == Some{Pr.work(seen)} : Maybe<&2, Nat>}) -> {Ch.look(cfg, w, e, Ch.Busy{Some{Pr.work(List.append(&2, Nat, seen, seg))}}) == Ch.Watch{Ch.W.fresh(cfg, Some{Pr.work(List.append(&2, Nat, seen, seg))})} : Ch.Next}:
  +b = Pr.work(List.append(&2, Nat, seen, seg))
  LChild.pc.progress_is_not_a_stall(cfg, w, e, b, pp.news(w, Pr.work(seen), b, tok, LA.pp.new_work(seen, seg, x, fresh, i)))

def Progress.child_new_work_is_progress(cfg, w, e, seen, seg, x, fresh, news, tok):
  pp.new_work_moves(cfg, w, e, seen, seg, x, fresh, news, tok)
