# eukhe: the proof of LAW thread_request_prefix_kept
#
# PROOF: the second call keeps the first call's pin: a pin is rendered
# under the call's head, so a call under that head keeps it (tpk.pin_twice).
# Both requests are then trq.request (trq.is_request) over one view v.
# The chat of evs ++ more is the chat of evs, then the chat of more
# (tpk.chat_app), so its length is T + k (tpk.len_app) and end stays
# (T + k) - (w + k) = T - w (tpk.sub_add). The kept lines of v end within
# the chat of evs (tpk.kept_inside), so each covers the same messages over
# the longer chat (tpk.lines, tpk.line, tpk.take_app); the drop at end, at
# most T (tnv.sub_le), keeps the old rest and appends the new messages
# (tpk.drop_app), whose turns come last (tpk.turns_app, tpk.assoc).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA
import ./thread_newest_verbatim.bend as PThreadNewestVerbatim
import ./base/request.bend as RQ

# Pins
# ----

def tpk.pin_twice.go(b: Bool, +h0: Nat, +v: List<&2, Th.Span>, +h: Nat, +f1: List<&2, Th.Span>, +f2: List<&2, Th.Span>, e: {Nat.is_eq(h0, h) == b : Bool}) -> {Th.pin.keep(b, Th.Pin{h0, v}, h, f1) == Th.pin(Th.pin.keep(b, Th.Pin{h0, v}, h, f1), h, f2) : Th.Pin}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(h0, h), True{}, e) : {Th.Pin{h0, v} == Th.pin.keep(_, Th.Pin{h0, v}, h, f2) : Th.Pin}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, LA.thb.eq_refl(h)) : {Th.Pin{h, f1} == Th.pin.keep(_, Th.Pin{h, f1}, h, f2) : Th.Pin}
      {==}

# a call under the head of the pin it just made keeps it
def tpk.pin_twice(p: Th.Pin, +h: Nat, +f1: List<&2, Th.Span>, +f2: List<&2, Th.Span>) -> {Th.pin(p, h, f1) == Th.pin(Th.pin(p, h, f1), h, f2) : Th.Pin}:
  match p:
    case Th.Pin{+h0, +v}:
      tpk.pin_twice.go(Nat.is_eq(h0, h), h0, v, h, f1, f2, {==})

# Lists
# -----

def tpk.assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %tpk.assoc(A, t, ys, zs) : {x <> List.append(&2, A, List.append(&2, A, t, ys), zs) == x <> _ : List<&2, A>}
      {==}

def tpk.len_app(xs: List<&2, Th.Msg>, +ys: List<&2, Th.Msg>) -> {List.length(&2, Th.Msg, List.append(&2, Th.Msg, xs, ys)) == Nat.add(List.length(&2, Th.Msg, xs), List.length(&2, Th.Msg, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %tpk.len_app(t, ys) : {1n+List.length(&2, Th.Msg, List.append(&2, Th.Msg, t, ys)) == 1n+_ : Nat}
      {==}

def tpk.drop_zero(xs: List<&2, Th.Msg>) -> {List.drop(&2, Th.Msg, xs, 0n) == xs : List<&2, Th.Msg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def tpk.take_zero(xs: List<&2, Th.Msg>) -> {List.take(&2, Th.Msg, xs, 0n) == Nil{} : List<&2, Th.Msg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

# a take within xs ignores what follows xs
def tpk.take_app(xs: List<&2, Th.Msg>, +ys: List<&2, Th.Msg>, c: Nat, h: {Nat.is_le(c, List.length(&2, Th.Msg, xs)) == True{} : Bool}) -> {List.take(&2, Th.Msg, List.append(&2, Th.Msg, xs, ys), c) == List.take(&2, Th.Msg, xs, c) : List<&2, Th.Msg>}:
  match xs c:
    case Nil{} 0n:
      tpk.take_zero(ys)
    case Nil{} 1n+p:
      LA.thb.absurd_ft({List.take(&2, Th.Msg, ys, 1n+p) == Nil{} : List<&2, Th.Msg>}, h)
    case x <> t 0n:
      {==}
    case +x <> +t 1n++p:
      %tpk.take_app(t, ys, p, h) : {x <> List.take(&2, Th.Msg, List.append(&2, Th.Msg, t, ys), p) == x <> _ : List<&2, Th.Msg>}
      {==}

# a drop within xs keeps what follows xs after its rest
def tpk.drop_app(xs: List<&2, Th.Msg>, +ys: List<&2, Th.Msg>, e: Nat, h: {Nat.is_le(e, List.length(&2, Th.Msg, xs)) == True{} : Bool}) -> {List.drop(&2, Th.Msg, List.append(&2, Th.Msg, xs, ys), e) == List.append(&2, Th.Msg, List.drop(&2, Th.Msg, xs, e), ys) : List<&2, Th.Msg>}:
  match xs e:
    case Nil{} 0n:
      tpk.drop_zero(ys)
    case Nil{} 1n+p:
      LA.thb.absurd_ft({List.drop(&2, Th.Msg, ys, 1n+p) == ys : List<&2, Th.Msg>}, h)
    case x <> t 0n:
      {==}
    case x <> +t 1n+p:
      tpk.drop_app(t, ys, p, h)

# a line that ends within ch covers the same messages of ch ++ ys
def tpk.line(st: Nat, ch: List<&2, Th.Msg>, +ys: List<&2, Th.Msg>, +c: Nat, h: {Nat.is_le(Nat.add(st, c), List.length(&2, Th.Msg, ch)) == True{} : Bool}) -> {List.take(&2, Th.Msg, List.drop(&2, Th.Msg, List.append(&2, Th.Msg, ch, ys), st), c) == List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ch, st), c) : List<&2, Th.Msg>}:
  match st ch:
    case 0n Nil{}:
      %Equal.sym(List<&2, Th.Msg>, List.drop(&2, Th.Msg, ys, 0n), ys, tpk.drop_zero(ys)) : {List.take(&2, Th.Msg, _, c) == Nil{} : List<&2, Th.Msg>}
      tpk.take_app(Nil{}, ys, c, h)
    case 0n x <> t:
      tpk.take_app(x <> t, ys, c, h)
    case 1n+p Nil{}:
      LA.thb.absurd_ft({List.take(&2, Th.Msg, List.drop(&2, Th.Msg, ys, 1n+p), c) == Nil{} : List<&2, Th.Msg>}, h)
    case 1n+p x <> t:
      tpk.line(p, t, ys, c, h)

# every line of a view that ends within ch covers the same messages of
# ch ++ ys
def tpk.lines(+ch: List<&2, Th.Msg>, +ys: List<&2, Th.Msg>, view: List<&2, Th.Span>, +h: {Thread.sp_inside(List.length(&2, Th.Msg, ch), view) == True{} : Bool}) -> {RQ.trq.lines(List.append(&2, Th.Msg, ch, ys), view) == RQ.trq.lines(ch, view) : List<&2, Th.Item>}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          +n = List.length(&2, Th.Msg, ch)
          +hl = LA.thb.and_l(Nat.is_le(Nat.add(st, c), n), Thread.sp_inside(n, t), h)
          +hr = LA.thb.and_r(Nat.is_le(Nat.add(st, c), n), Thread.sp_inside(n, t), h)
          +a = List.take(&2, Th.Msg, List.drop(&2, Th.Msg, List.append(&2, Th.Msg, ch, ys), st), c)
          %tpk.line(st, ch, ys, c, hl) : {Th.Line{st, a} <> RQ.trq.lines(List.append(&2, Th.Msg, ch, ys), t) == Th.Line{st, _} <> RQ.trq.lines(ch, t) : List<&2, Th.Item>}
          %tpk.lines(ch, ys, t, hr) : {Th.Line{st, a} <> RQ.trq.lines(List.append(&2, Th.Msg, ch, ys), t) == Th.Line{st, a} <> _ : List<&2, Th.Item>}
          {==}

def tpk.kept_inside.step(b: Bool, +n: Nat, +sp: Th.Span, -t: List<&2, Th.Span>, hs: {Thread.sp_inside(n, [sp]) == True{} : Bool}, ih: {Thread.sp_inside(n, t) == True{} : Bool}) -> {Thread.sp_inside(n, RQ.trq.keep.span(b, sp, t)) == True{} : Bool}:
  match b:
    case True{}:
      match sp:
        case Th.Span{+st, +c}:
          LA.thb.and_i(Nat.is_le(Nat.add(st, c), n), Thread.sp_inside(n, t), LA.thb.and_l(Nat.is_le(Nat.add(st, c), n), True{}, hs), ih)
    case False{}:
      {==}

# the kept lines of a view inside the chat are inside it
def tpk.kept_inside(+n: Nat, +e: Nat, view: List<&2, Th.Span>, +h: {Thread.sp_inside(n, view) == True{} : Bool}) -> {Thread.sp_inside(n, RQ.trq.kept(e, view)) == True{} : Bool}:
  match view:
    case Nil{}:
      {==}
    case sp <> +t:
      match sp:
        case Th.Span{+st, +c}:
          +hl = LA.thb.and_l(Nat.is_le(Nat.add(st, c), n), Thread.sp_inside(n, t), h)
          +hr = LA.thb.and_r(Nat.is_le(Nat.add(st, c), n), Thread.sp_inside(n, t), h)
          +hs = LA.thb.and_i(Nat.is_le(Nat.add(st, c), n), True{}, hl, {==})
          tpk.kept_inside.step(Nat.is_lt(st, e), n, Th.Span{st, c}, RQ.trq.kept(e, t), hs, tpk.kept_inside(n, e, t, hr))

# the chat of two streams is the chat of each, in order
def tpk.chat_app(+s: Nat, a: List<&2, Th.Msg>, +b: List<&2, Th.Msg>) -> {S.chat(s, List.append(&2, Th.Msg, a, b)) == List.append(&2, Th.Msg, S.chat(s, a), S.chat(s, b)) : List<&2, Th.Msg>}:
  match a:
    case Nil{}:
      {==}
    case +m <> +t:
      +o = S.only(S.mine(s, m), m)
      %Equal.sym(List<&2, Th.Msg>, S.chat(s, List.append(&2, Th.Msg, t, b)), List.append(&2, Th.Msg, S.chat(s, t), S.chat(s, b)), tpk.chat_app(s, t, b)) : {List.append(&2, Th.Msg, o, _) == List.append(&2, Th.Msg, List.append(&2, Th.Msg, o, S.chat(s, t)), S.chat(s, b)) : List<&2, Th.Msg>}
      Equal.sym(List<&2, Th.Msg>, List.append(&2, Th.Msg, List.append(&2, Th.Msg, o, S.chat(s, t)), S.chat(s, b)), List.append(&2, Th.Msg, o, List.append(&2, Th.Msg, S.chat(s, t), S.chat(s, b))), tpk.assoc(Th.Msg, o, S.chat(s, t), S.chat(s, b)))

def tpk.turns_app(a: List<&2, Th.Msg>, +b: List<&2, Th.Msg>) -> {S.turns(List.append(&2, Th.Msg, a, b)) == List.append(&2, Th.Item, S.turns(a), S.turns(b)) : List<&2, Th.Item>}:
  match a:
    case Nil{}:
      {==}
    case +m <> +t:
      %tpk.turns_app(t, b) : {Th.Turn{m} <> S.turns(List.append(&2, Th.Msg, t, b)) == Th.Turn{m} <> _ : List<&2, Th.Item>}
      {==}

# Arithmetic
# ----------

def tpk.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %tpk.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def tpk.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %tpk.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def tpk.sub_self(k: Nat) -> {Nat.sub(k, k) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      tpk.sub_self(j)

# k - (1 + q + k) = 0
def tpk.sub_over(k: Nat, +q: Nat) -> {Nat.sub(k, 1n+Nat.add(q, k)) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      %Equal.sym(Nat, Nat.add(q, 1n+j), 1n+Nat.add(q, j), tpk.add_succ(q, j)) : {Nat.sub(j, _) == 0n : Nat}
      tpk.sub_over(j, q)

# (1 + p + k) - k = 1 + p
def tpk.sub_back(+p: Nat, k: Nat) -> {Nat.sub(1n+Nat.add(p, k), k) == 1n+p : Nat}:
  match k:
    case 0n:
      %tpk.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++j:
      %Equal.sym(Nat, Nat.add(p, 1n+j), 1n+Nat.add(p, j), tpk.add_succ(p, j)) : {Nat.sub(_, j) == 1n+p : Nat}
      tpk.sub_back(p, j)

# (a + k) - (b + k) = a - b
def tpk.sub_add(a: Nat, b: Nat, +k: Nat) -> {Nat.sub(Nat.add(a, k), Nat.add(b, k)) == Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      tpk.sub_self(k)
    case 0n 1n+q:
      tpk.sub_over(k, q)
    case 1n+p 0n:
      tpk.sub_back(p, k)
    case 1n+p 1n+q:
      tpk.sub_add(p, q, k)

# The requests
# ------------

# over one view inside the chat of evs, the spec's request after more
# events, the window grown by the session's new messages, is the spec's
# request before them, then the new messages' turns
def tpk.core(+s: Nat, +evs: List<&2, Th.Msg>, +more: List<&2, Th.Msg>, +v: List<&2, Th.Span>, +w: Nat, inside: {Thread.sp_inside(List.length(&2, Th.Msg, S.chat(s, evs)), v) == True{} : Bool}) -> {RQ.trq.request(s, List.append(&2, Th.Msg, evs, more), v, Nat.add(w, List.length(&2, Th.Msg, S.chat(s, more)))) == List.append(&2, Th.Item, RQ.trq.request(s, evs, v, w), S.turns(S.chat(s, more))) : List<&2, Th.Item>}:
  +ch = S.chat(s, evs)
  +cm = S.chat(s, more)
  +k = List.length(&2, Th.Msg, cm)
  +t = List.length(&2, Th.Msg, ch)
  +e = Nat.sub(t, w)
  +app = List.append(&2, Th.Msg, ch, cm)
  +old = RQ.trq.lines(ch, RQ.trq.kept(e, v))
  +rest = S.turns(List.drop(&2, Th.Msg, ch, e))
  +goal = List.append(&2, Th.Item, List.append(&2, Th.Item, old, rest), S.turns(cm))
  %Equal.sym(List<&2, Th.Msg>, S.chat(s, List.append(&2, Th.Msg, evs, more)), app, tpk.chat_app(s, evs, more)) : {List.append(&2, Th.Item, RQ.trq.lines(_, RQ.trq.kept(Nat.sub(List.length(&2, Th.Msg, _), Nat.add(w, k)), v)), S.turns(List.drop(&2, Th.Msg, _, Nat.sub(List.length(&2, Th.Msg, _), Nat.add(w, k))))) == goal : List<&2, Th.Item>}
  %Equal.sym(Nat, List.length(&2, Th.Msg, app), Nat.add(t, k), tpk.len_app(ch, cm)) : {List.append(&2, Th.Item, RQ.trq.lines(app, RQ.trq.kept(Nat.sub(_, Nat.add(w, k)), v)), S.turns(List.drop(&2, Th.Msg, app, Nat.sub(_, Nat.add(w, k))))) == goal : List<&2, Th.Item>}
  %Equal.sym(Nat, Nat.sub(Nat.add(t, k), Nat.add(w, k)), e, tpk.sub_add(t, w, k)) : {List.append(&2, Th.Item, RQ.trq.lines(app, RQ.trq.kept(_, v)), S.turns(List.drop(&2, Th.Msg, app, _))) == goal : List<&2, Th.Item>}
  %Equal.sym(List<&2, Th.Item>, RQ.trq.lines(app, RQ.trq.kept(e, v)), old, tpk.lines(ch, cm, RQ.trq.kept(e, v), tpk.kept_inside(t, e, v, inside))) : {List.append(&2, Th.Item, _, S.turns(List.drop(&2, Th.Msg, app, e))) == goal : List<&2, Th.Item>}
  %Equal.sym(List<&2, Th.Msg>, List.drop(&2, Th.Msg, app, e), List.append(&2, Th.Msg, List.drop(&2, Th.Msg, ch, e), cm), tpk.drop_app(ch, cm, e, PThreadNewestVerbatim.tnv.sub_le(t, w))) : {List.append(&2, Th.Item, old, S.turns(_)) == goal : List<&2, Th.Item>}
  %Equal.sym(List<&2, Th.Item>, S.turns(List.append(&2, Th.Msg, List.drop(&2, Th.Msg, ch, e), cm)), List.append(&2, Th.Item, rest, S.turns(cm)), tpk.turns_app(List.drop(&2, Th.Msg, ch, e), cm)) : {List.append(&2, Th.Item, old, _) == goal : List<&2, Th.Item>}
  Equal.sym(List<&2, Th.Item>, goal, List.append(&2, Th.Item, old, List.append(&2, Th.Item, rest, S.turns(cm))), tpk.assoc(Th.Item, old, rest, S.turns(cm)))

def Thread.thread_request_prefix_kept(s, evs, more, p, h, fresh, again, w, inside):
  +v = Thread.sp_view(Th.pin(p, h, fresh))
  +cm = S.chat(s, more)
  +k = List.length(&2, Th.Msg, cm)
  +evs2 = List.append(&2, Th.Msg, evs, more)
  +rhs = List.append(&2, Th.Item, Th.request(s, evs, v, w), S.turns(cm))
  %tpk.pin_twice(p, h, fresh, again) : {Th.request(s, evs2, Thread.sp_view(_), Nat.add(w, k)) == rhs : List<&2, Th.Item>}
  Equal.trans(List<&2, Th.Item>, Th.request(s, evs2, v, Nat.add(w, k)), RQ.trq.request(s, evs2, v, Nat.add(w, k)), rhs, RQ.trq.is_request(s, evs2, v, Nat.add(w, k)), Equal.trans(List<&2, Th.Item>, RQ.trq.request(s, evs2, v, Nat.add(w, k)), List.append(&2, Th.Item, RQ.trq.request(s, evs, v, w), S.turns(cm)), rhs, tpk.core(s, evs, more, v, w, inside), Equal.cong(List<&2, Th.Item>, List<&2, Th.Item>, x => List.append(&2, Th.Item, x, S.turns(cm)), RQ.trq.request(s, evs, v, w), Th.request(s, evs, v, w), Equal.sym(List<&2, Th.Item>, Th.request(s, evs, v, w), RQ.trq.request(s, evs, v, w), RQ.trq.is_request(s, evs, v, w)))))
