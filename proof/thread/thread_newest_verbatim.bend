# eukhe: the proof of LAW thread_newest_verbatim
#
# PROOF: the witnesses: hist = the request's view lines, old = the chat's
# first end messages, new = the rest. The request appends the turns of the
# rest of its log after its lines; the log is the spec's chat
# (thb.log_chat) and the model's turns are the spec's (tnv.turns). View
# lines hold no turn (tnv.no_turns). A take and a drop at one place append
# back to the list (tnv.take_drop), and end is at most the chat's length,
# so the take holds exactly end messages (tnv.sub_le, tnv.len_take).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def tnv.turns(ms: List<&2, Th.Msg>) -> {Th.turns(ms) == S.turns(ms) : List<&2, Th.Item>}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +t:
      %tnv.turns(t) : {Th.Turn{m} <> Th.turns(t) == Th.Turn{m} <> _ : List<&2, Th.Item>}
      {==}

def tnv.no_turns(+lg: List<&2, Th.Msg>, view: List<&2, Th.Span>) -> {S.no_turns(Th.lines(lg, view)) == True{} : Bool}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{st, c}:
          tnv.no_turns(lg, t)

def tnv.take_drop(xs: List<&2, Th.Msg>, n: Nat) -> {List.append(&2, Th.Msg, List.take(&2, Th.Msg, xs, n), List.drop(&2, Th.Msg, xs, n)) == xs : List<&2, Th.Msg>}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case +x <> +t 1n+p:
      %tnv.take_drop(t, p) : {x <> List.append(&2, Th.Msg, List.take(&2, Th.Msg, t, p), List.drop(&2, Th.Msg, t, p)) == x <> _ : List<&2, Th.Msg>}
      {==}

def tnv.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      tnv.le_refl(p)

def tnv.le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+x 0n:
      LA.thb.absurd_ft({Nat.is_le(1n+x, 1n) == True{} : Bool}, h)
    case 1n+x 1n+y:
      tnv.le_step(x, y, h)

# t - w is at most t
def tnv.sub_le(t: Nat, w: Nat) -> {Nat.is_le(Nat.sub(t, w), t) == True{} : Bool}:
  match t w:
    case 0n _:
      {==}
    case 1n+p 0n:
      tnv.le_refl(p)
    case 1n++p 1n++q:
      tnv.le_step(Nat.sub(p, q), p, tnv.sub_le(p, q))

# a take of at most the list's length holds that many items
def tnv.len_take(xs: List<&2, Th.Msg>, n: Nat, h: {Nat.is_le(n, List.length(&2, Th.Msg, xs)) == True{} : Bool}) -> {List.length(&2, Th.Msg, List.take(&2, Th.Msg, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      LA.thb.absurd_ft({List.length(&2, Th.Msg, List.take(&2, Th.Msg, Nil{}, 1n+p)) == 1n+p : Nat}, h)
    case x <> t 0n:
      {==}
    case x <> +t 1n+p:
      %tnv.len_take(t, p, h) : {1n+List.length(&2, Th.Msg, List.take(&2, Th.Msg, t, p)) == 1n+_ : Nat}
      {==}

# the request is its lines, then the turns of the chat's rest
def tnv.req(+s: Nat, +evs: List<&2, Th.Msg>, +view: List<&2, Th.Span>, +w: Nat) -> {Th.request(s, evs, view, w) == List.append(&2, Th.Item, Th.lines(Th.log(s, evs), List.take(&2, Th.Span, view, Th.history_lines(List.length(&2, Th.Msg, Th.log(s, evs)), w, Th.starts(view)))), S.turns(List.drop(&2, Th.Msg, S.chat(s, evs), Nat.sub(List.length(&2, Th.Msg, S.chat(s, evs)), w)))) : List<&2, Th.Item>}:
  +lg = Th.log(s, evs)
  +hist = Th.lines(lg, List.take(&2, Th.Span, view, Th.history_lines(List.length(&2, Th.Msg, lg), w, Th.starts(view))))
  %LA.thb.log_chat(s, evs) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, hist, S.turns(List.drop(&2, Th.Msg, _, Nat.sub(List.length(&2, Th.Msg, _), w)))) : List<&2, Th.Item>}
  %tnv.turns(List.drop(&2, Th.Msg, lg, Nat.sub(List.length(&2, Th.Msg, lg), w))) : {Th.request(s, evs, view, w) == List.append(&2, Th.Item, hist, _) : List<&2, Th.Item>}
  {==}

def Thread.thread_newest_verbatim(s, evs, view, w):
  +lg = Th.log(s, evs)
  +ch = S.chat(s, evs)
  +kept = List.take(&2, Th.Span, view, Th.history_lines(List.length(&2, Th.Msg, lg), w, Th.starts(view)))
  +e = Nat.sub(List.length(&2, Th.Msg, ch), w)
  +ec = Equal.sym(List<&2, Th.Msg>, List.append(&2, Th.Msg, List.take(&2, Th.Msg, ch, e), List.drop(&2, Th.Msg, ch, e)), ch, tnv.take_drop(ch, e))
  +en = tnv.len_take(ch, e, tnv.sub_le(List.length(&2, Th.Msg, ch), w))
  (Th.lines(lg, kept), (List.take(&2, Th.Msg, ch, e), (List.drop(&2, Th.Msg, ch, e), (tnv.req(s, evs, view, w), (tnv.no_turns(lg, kept), (ec, en))))))
