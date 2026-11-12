# eukhe: a lemma of the proofs of area thread: the model's request
# (bend/thread.bend) restated as the leading view lines that start before
# end, each over its own span, then the turns of the chat from end on
# (trq.request), with the proof that the model computes it
# (trq.is_request). A proof step of thread_request_prefix_kept, not a law:
# the laws state the request by thread_request_lines and
# thread_newest_verbatim.

import Base
import ../../../bend/thread.bend as Th
import ../../../spec/memory/thread.bend as S
import ../base.bend as LA
import ../thread_newest_verbatim.bend as PThreadNewestVerbatim

def trq.keep.span(b: Bool, sp: Th.Span, rest: List<&2, Th.Span>) -> List<&2, Th.Span>:
  match b:
    case True{}:
      sp <> rest
    case False{}:
      Nil{}

# the leading lines of a view that start before e: the lines kept
def trq.kept(+e: Nat, view: List<&2, Th.Span>) -> List<&2, Th.Span>:
  match view:
    case Nil{}:
      Nil{}
    case sp <> t:
      match sp:
        case Th.Span{+st, c}:
          trq.keep.span(Nat.is_lt(st, e), Th.Span{st, c}, trq.kept(e, t))

def trq.line(+ch: List<&2, Th.Msg>, sp: Th.Span) -> Th.Item:
  match sp:
    case Th.Span{+st, c}:
      Th.Line{st, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c)}

def trq.lines(+ch: List<&2, Th.Msg>, view: List<&2, Th.Span>) -> List<&2, Th.Item>:
  match view:
    case Nil{}:
      Nil{}
    case sp <> t:
      trq.line(ch, sp) <> trq.lines(ch, t)

def trq.request(+s: Nat, evs: List<&2, Th.Msg>, view: List<&2, Th.Span>, +w: Nat) -> List<&2, Th.Item>:
  +ch = S.chat(s, evs)
  +e = S.end(ch, w)
  List.append(&2, Th.Item, trq.lines(ch, trq.kept(e, view)), S.turns(List.drop(&2, Th.Msg, ch, e)))

def trs.lines(+ch: List<&2, Th.Msg>, view: List<&2, Th.Span>) -> {Th.lines(ch, view) == trq.lines(ch, view) : List<&2, Th.Item>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          %trs.lines(ch, t) : {Th.Line{st, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c)} <> Th.lines(ch, t) == Th.Line{st, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c)} <> _ : List<&2, Th.Item>}
          {==}

def trs.step(b: Bool, +sp: Th.Span, +t: List<&2, Th.Span>, +n: Nat, -k: List<&2, Th.Span>, ih: {List.take(&2, Th.Span, t, n) == k : List<&2, Th.Span>}) -> {List.take(&2, Th.Span, sp <> t, Th.history_lines.step(b, n)) == trq.keep.span(b, sp, k) : List<&2, Th.Span>}:
  match b:
    case True{}:
      %ih : {sp <> List.take(&2, Th.Span, t, n) == sp <> _ : List<&2, Th.Span>}
      {==}
    case False{}:
      {==}

def trs.kept(view: List<&2, Th.Span>, +e: Nat) -> {List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e)) == trq.kept(e, view) : List<&2, Th.Span>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          trs.step(Nat.is_lt(st, e), Th.Span{st, c}, t, Th.history_lines.go(Th.starts(t), e), trq.kept(e, t), trs.kept(t, e))

# the model computes trq.request: its log is the spec's chat
# (thb.log_chat), its turns the spec's (tnv.turns); taking the count of
# leading starts below end keeps the leading lines below end (trs.kept),
# each built from its own start (trs.lines)
def trq.is_request(+s: Nat, +evs: List<&2, Th.Msg>, +view: List<&2, Th.Span>, +w: Nat) -> {Th.request(s, evs, view, w) == trq.request(s, evs, view, w) : List<&2, Th.Item>}:
  +ch = S.chat(s, evs)
  +e = Nat.sub(List.length(&2, Th.Msg, ch), w)
  %trs.lines(ch, trq.kept(e, view)) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, _, S.turns(List.drop(&2, Th.Msg, ch, e))) : List<&2, Th.Item>}
  %trs.kept(view, e) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(ch, _), S.turns(List.drop(&2, Th.Msg, ch, e))) : List<&2, Th.Item>}
  %PThreadNewestVerbatim.tnv.turns(List.drop(&2, Th.Msg, ch, e)) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e))), _) : List<&2, Th.Item>}
  %LA.thb.log_chat(s, evs) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(_, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), Nat.sub(List.length(&2, Th.Msg, _), w)))), Th.turns(List.drop(&2, Th.Msg, _, Nat.sub(List.length(&2, Th.Msg, _), w)))) : List<&2, Th.Item>}
  {==}
