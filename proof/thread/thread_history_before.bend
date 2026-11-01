# eukhe: the proof of LAW thread_history_before
#
# PROOF: end is the log's (thread_log_chat). By induction on the view
# (thb_k.view), the kept lines are the leading ones the count walks: each
# counted line starts before end (the step counts it only then), and the
# walk stops at the first that does not. Turns are no view line
# (thb_k.turns), and an append of two such lists is one (thb_k.app).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA
import ./thread_log_chat.bend as PThreadLogChat

def thb_k.app(+e: Nat, a: List<&2, Th.Item>, +b: List<&2, Th.Item>, ha: {S.lines_before(e, a) == True{} : Bool}, hb: {S.lines_before(e, b) == True{} : Bool}) -> {S.lines_before(e, List.append(&2, Th.Item, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +it <> +t:
      +hh = ha
      LA.thb.and_i(S.item_before(e, it), S.lines_before(e, List.append(&2, Th.Item, t, b)), LA.thb.and_l(S.item_before(e, it), S.lines_before(e, t), hh), thb_k.app(e, t, b, LA.thb.and_r(S.item_before(e, it), S.lines_before(e, t), hh), hb))

def thb_k.turns(+e: Nat, ms: List<&2, Th.Msg>) -> {S.lines_before(e, Th.turns(ms)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case m <> t:
      thb_k.turns(e, t)

def thb_k.step(b: Bool, +lg: List<&2, Th.Msg>, +st: Nat, +c: Nat, +t: List<&2, Th.Span>, +e: Nat, eb: {Nat.is_lt(st, e) == b : Bool}, ih: {S.lines_before(e, Th.lines(lg, List.take(&2, Th.Span, t, Th.history_lines.go(Th.starts(t), e)))) == True{} : Bool}) -> {S.lines_before(e, Th.lines(lg, List.take(&2, Th.Span, Th.Span{st, c} <> t, Th.history_lines.step(b, Th.history_lines.go(Th.starts(t), e))))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(st, e), True{}, eb) : {Bool.and(_, S.lines_before(e, Th.lines(lg, List.take(&2, Th.Span, t, Th.history_lines.go(Th.starts(t), e))))) == True{} : Bool}
      ih
    case False{}:
      {==}

# every kept line starts before end
def thb_k.view(+lg: List<&2, Th.Msg>, view: List<&2, Th.Span>, +e: Nat) -> {S.lines_before(e, Th.lines(lg, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e)))) == True{} : Bool}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          thb_k.step(Nat.is_lt(st, e), lg, st, c, t, e, {==}, thb_k.view(lg, t, e))

def Thread.thread_history_before(s, evs, view, w):
  +lg = Th.log(s, evs)
  +e = Nat.sub(List.length(&2, Th.Msg, lg), w)
  %Thread.thread_log_chat(s, evs) : {S.lines_before(S.end(_, w), Th.request(s, evs, view, w)) == True{} : Bool}
  thb_k.app(e, Th.lines(lg, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e))), Th.turns(List.drop(&2, Th.Msg, lg, e)), thb_k.view(lg, view, e), thb_k.turns(e, List.drop(&2, Th.Msg, lg, e)))
