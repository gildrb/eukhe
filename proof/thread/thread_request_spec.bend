# eukhe: the proof of LAW thread_request_spec
#
# PROOF: both sides are the kept view lines, then the turns of the chat
# from end on. The model's log is the spec's chat (thread_log_chat) and its
# turns are the spec's (tnv.turns). Taking the count of leading starts
# below end from the view keeps exactly the spec's leading lines below end
# (trs.kept, by induction on the view and cases on the comparison: trs.step).
# The model builds each line as the spec does, from its own start
# (trs.lines, by induction on the kept lines).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./thread_log_chat.bend as PThreadLogChat
import ./thread_newest_verbatim.bend as PThreadNewestVerbatim

def trs.lines(+ch: List<&2, Th.Msg>, view: List<&2, Th.Span>) -> {Th.lines(ch, view) == S.lines(ch, view) : List<&2, Th.Item>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          %trs.lines(ch, t) : {Th.Line{st, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c)} <> Th.lines(ch, t) == Th.Line{st, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c)} <> _ : List<&2, Th.Item>}
          {==}

def trs.step(b: Bool, +sp: Th.Span, +t: List<&2, Th.Span>, +n: Nat, -k: List<&2, Th.Span>, ih: {List.take(&2, Th.Span, t, n) == k : List<&2, Th.Span>}) -> {List.take(&2, Th.Span, sp <> t, Th.history_lines.step(b, n)) == S.keep.span(b, sp, k) : List<&2, Th.Span>}:
  match b:
    case True{}:
      %ih : {sp <> List.take(&2, Th.Span, t, n) == sp <> _ : List<&2, Th.Span>}
      {==}
    case False{}:
      {==}

def trs.kept(view: List<&2, Th.Span>, +e: Nat) -> {List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e)) == S.kept(e, view) : List<&2, Th.Span>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          trs.step(Nat.is_lt(st, e), Th.Span{st, c}, t, Th.history_lines.go(Th.starts(t), e), S.kept(e, t), trs.kept(t, e))

def Thread.thread_request_spec(s, evs, view, w):
  +ch = S.chat(s, evs)
  +e = Nat.sub(List.length(&2, Th.Msg, ch), w)
  %trs.lines(ch, S.kept(e, view)) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, _, S.turns(List.drop(&2, Th.Msg, ch, e))) : List<&2, Th.Item>}
  %trs.kept(view, e) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(ch, _), S.turns(List.drop(&2, Th.Msg, ch, e))) : List<&2, Th.Item>}
  %PThreadNewestVerbatim.tnv.turns(List.drop(&2, Th.Msg, ch, e)) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e))), _) : List<&2, Th.Item>}
  %Thread.thread_log_chat(s, evs) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(_, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), Nat.sub(List.length(&2, Th.Msg, _), w)))), Th.turns(List.drop(&2, Th.Msg, _, Nat.sub(List.length(&2, Th.Msg, _), w)))) : List<&2, Th.Item>}
  {==}
