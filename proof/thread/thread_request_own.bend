# eukhe: the proof of LAW thread_request_own
#
# PROOF: the session wrote every message of its chat (tro.log: a message
# is kept only when its session is s); a slice of the chat (a drop, then a
# take) keeps only messages of the chat (tro.drop, tro.take), so every
# view line's covered messages are the session's (tro.lines), and so is
# every turn of the transcript (tro.turns); a request appends the two
# (tro.app).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def tro.keep(b: Bool, +s: Nat, +who: Nat, +body: Nat, rest: List<&2, Th.Msg>, eb: {Nat.is_eq(who, s) == b : Bool}, hr: {S.own(s, rest) == True{} : Bool}) -> {S.own(s, Th.log.keep(b, Th.Msg{who, body}, rest)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(who, s), True{}, eb) : {Bool.and(_, S.own(s, rest)) == True{} : Bool}
      hr
    case False{}:
      hr

# session s wrote every message of its chat
def tro.log(+s: Nat, evs: List<&2, Th.Msg>) -> {S.own(s, Th.log(s, evs)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Th.Msg{+who, +body}:
          tro.keep(Nat.is_eq(who, s), s, who, body, Th.log(s, t), {==}, tro.log(s, t))

def tro.drop(+s: Nat, xs: List<&2, Th.Msg>, n: Nat, h: {S.own(s, xs) == True{} : Bool}) -> {S.own(s, List.drop(&2, Th.Msg, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> t 0n:
      h
    case +x <> +t 1n+p:
      tro.drop(s, t, p, LA.thb.and_r(S.mine(s, x), S.own(s, t), h))

def tro.take(+s: Nat, xs: List<&2, Th.Msg>, n: Nat, h: {S.own(s, xs) == True{} : Bool}) -> {S.own(s, List.take(&2, Th.Msg, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case +x <> +t 1n+p:
      +hh = h
      LA.thb.and_i(S.mine(s, x), S.own(s, List.take(&2, Th.Msg, t, p)), LA.thb.and_l(S.mine(s, x), S.own(s, t), hh), tro.take(s, t, p, LA.thb.and_r(S.mine(s, x), S.own(s, t), hh)))

# every view line over the chat covers only the session's messages
def tro.lines(+s: Nat, +lg: List<&2, Th.Msg>, view: List<&2, Th.Span>, +h: {S.own(s, lg) == True{} : Bool}) -> {S.items_own(s, Th.lines(lg, view)) == True{} : Bool}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          +ow = tro.take(s, List.drop(&2, Th.Msg, lg, st), c, tro.drop(s, lg, st, h))
          LA.thb.and_i(S.own(s, List.take(&2, Th.Msg, List.drop(&2, Th.Msg, lg, st), c)), S.items_own(s, Th.lines(lg, t)), ow, tro.lines(s, lg, t, h))

# every turn of the session's messages is the session's
def tro.turns(+s: Nat, ms: List<&2, Th.Msg>, h: {S.own(s, ms) == True{} : Bool}) -> {S.items_own(s, Th.turns(ms)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +t:
      +hh = h
      LA.thb.and_i(S.mine(s, m), S.items_own(s, Th.turns(t)), LA.thb.and_l(S.mine(s, m), S.own(s, t), hh), tro.turns(s, t, LA.thb.and_r(S.mine(s, m), S.own(s, t), hh)))

def tro.app(+s: Nat, a: List<&2, Th.Item>, +b: List<&2, Th.Item>, ha: {S.items_own(s, a) == True{} : Bool}, hb: {S.items_own(s, b) == True{} : Bool}) -> {S.items_own(s, List.append(&2, Th.Item, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +it <> +t:
      +hh = ha
      LA.thb.and_i(S.item_own(s, it), S.items_own(s, List.append(&2, Th.Item, t, b)), LA.thb.and_l(S.item_own(s, it), S.items_own(s, t), hh), tro.app(s, t, b, LA.thb.and_r(S.item_own(s, it), S.items_own(s, t), hh), hb))

def Thread.thread_request_own(s, evs, view, w):
  +lg = Th.log(s, evs)
  +hl = tro.log(s, evs)
  +total = List.length(&2, Th.Msg, lg)
  +kept = List.take(&2, Th.Span, view, Th.history_lines(total, w, Th.starts(view)))
  +tail = List.drop(&2, Th.Msg, lg, Nat.sub(total, w))
  tro.app(s, Th.lines(lg, kept), Th.turns(tail), tro.lines(s, lg, kept, hl), tro.turns(s, tail, tro.drop(s, lg, Nat.sub(total, w), hl)))
