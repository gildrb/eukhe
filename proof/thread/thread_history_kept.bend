# eukhe: the proof of LAW thread_history_kept
#
# PROOF: end is the log's (thread_log_chat); the turns add no line start
# (thk.turns, thk.app). By induction on the view (thk.view): a line that
# starts before end is kept, as the spec keeps it; at the first line that
# does not, the walk stops, and since the starts ascend no later start is
# before end either (thk.none: a start at least one not before end is not
# before end, thk.le_lt), so the spec keeps nothing more.

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA
import ./thread_log_chat.bend as PThreadLogChat

def thk.app(a: List<&2, Th.Item>, +b: List<&2, Th.Item>) -> {S.line_starts(List.append(&2, Th.Item, a, b)) == List.append(&2, Nat, S.line_starts(a), S.line_starts(b)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case it <> +t:
      match it:
        case Th.Line{+st, ms}:
          %thk.app(t, b) : {st <> S.line_starts(List.append(&2, Th.Item, t, b)) == st <> _ : List<&2, Nat>}
          {==}
        case Th.Turn{m}:
          thk.app(t, b)

def thk.turns(ms: List<&2, Th.Msg>) -> {S.line_starts(Th.turns(ms)) == Nil{} : List<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case m <> t:
      thk.turns(t)

def thk.app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %thk.app_nil(t) : {x <> List.append(&2, Nat, t, Nil{}) == x <> _ : List<&2, Nat>}
      {==}

def thk.lt_zero(b: Nat) -> {Nat.is_lt(b, 0n) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a start at least one not before e is not before e
def thk.le_lt(a: Nat, b: Nat, e: Nat, hab: {Nat.is_le(a, b) == True{} : Bool}, hae: {Nat.is_lt(a, e) == False{} : Bool}) -> {Nat.is_lt(b, e) == False{} : Bool}:
  match a b e:
    case _ _ 0n:
      thk.lt_zero(b)
    case 0n _ 1n+f:
      LA.thb.absurd_tf({Nat.is_lt(b, 1n+f) == False{} : Bool}, hae)
    case 1n+p 0n 1n+f:
      LA.thb.absurd_ft({Nat.is_lt(0n, 1n+f) == False{} : Bool}, hab)
    case 1n+p 1n+q 1n+f:
      thk.le_lt(p, q, f, hab, hae)

# ascending after a start not before e: nothing more is before e
def thk.none(xs: List<&2, Nat>, +prev: Nat, +e: Nat, h: {S.ascending.go(xs, prev) == True{} : Bool}, hp: {Nat.is_lt(prev, e) == False{} : Bool}) -> {S.before(e, xs) == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +hh = h
      +hx = thk.le_lt(prev, x, e, LA.thb.and_l(Nat.is_le(prev, x), S.ascending.go(t, x), hh), hp)
      %Equal.sym(Bool, Nat.is_lt(x, e), False{}, hx) : {List.append(&2, Nat, S.below(_, x), S.before(e, t)) == Nil{} : List<&2, Nat>}
      thk.none(t, x, e, LA.thb.and_r(Nat.is_le(prev, x), S.ascending.go(t, x), hh), hx)

# the rest of an ascending list ascends
def thk.asc_tail(xs: List<&2, Nat>, +prev: Nat, h: {S.ascending.go(xs, prev) == True{} : Bool}) -> {S.ascending(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      LA.thb.and_r(Nat.is_le(prev, x), S.ascending.go(t, x), h)

def thk.step(b: Bool, +lg: List<&2, Th.Msg>, +st: Nat, +c: Nat, +t: List<&2, Th.Span>, +e: Nat, eb: {Nat.is_lt(st, e) == b : Bool}, asc: {S.ascending.go(S.view_starts(t), st) == True{} : Bool}, ih: {S.line_starts(Th.lines(lg, List.take(&2, Th.Span, t, Th.history_lines.go(Th.starts(t), e)))) == S.before(e, S.view_starts(t)) : List<&2, Nat>}) -> {S.line_starts(Th.lines(lg, List.take(&2, Th.Span, Th.Span{st, c} <> t, Th.history_lines.step(b, Th.history_lines.go(Th.starts(t), e))))) == List.append(&2, Nat, S.below(b, st), S.before(e, S.view_starts(t))) : List<&2, Nat>}:
  match b:
    case True{}:
      %ih : {st <> S.line_starts(Th.lines(lg, List.take(&2, Th.Span, t, Th.history_lines.go(Th.starts(t), e)))) == st <> _ : List<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Nat>, S.before(e, S.view_starts(t)), Nil{}, thk.none(S.view_starts(t), st, e, asc, eb)) : {Nil{} == _ : List<&2, Nat>}
      {==}

# the kept lines' starts are the view's starts before end
def thk.view(+lg: List<&2, Th.Msg>, view: List<&2, Th.Span>, +e: Nat, asc: {S.ascending(S.view_starts(view)) == True{} : Bool}) -> {S.line_starts(Th.lines(lg, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e)))) == S.before(e, S.view_starts(view)) : List<&2, Nat>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          +ha = asc
          thk.step(Nat.is_lt(st, e), lg, st, c, t, e, {==}, ha, thk.view(lg, t, e, thk.asc_tail(S.view_starts(t), st, ha)))

def Thread.thread_history_kept(s, evs, view, w, asc):
  +lg = Th.log(s, evs)
  +e = Nat.sub(List.length(&2, Th.Msg, lg), w)
  +hist = Th.lines(lg, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e)))
  +tail = Th.turns(List.drop(&2, Th.Msg, lg, e))
  %Thread.thread_log_chat(s, evs) : {S.line_starts(Th.request(s, evs, view, w)) == S.before(S.end(_, w), S.view_starts(view)) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, S.line_starts(List.append(&2, Th.Item, hist, tail)), List.append(&2, Nat, S.line_starts(hist), S.line_starts(tail)), thk.app(hist, tail)) : {_ == S.before(e, S.view_starts(view)) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, S.line_starts(tail), Nil{}, thk.turns(List.drop(&2, Th.Msg, lg, e))) : {List.append(&2, Nat, S.line_starts(hist), _) == S.before(e, S.view_starts(view)) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, S.line_starts(hist), Nil{}), S.line_starts(hist), thk.app_nil(S.line_starts(hist))) : {_ == S.before(e, S.view_starts(view)) : List<&2, Nat>}
  thk.view(lg, view, e, asc)
