# eukhe: the proof of LAW thread_request_lines
#
# PROOF: the model's log is the spec's chat (thb.log_chat). By induction
# on the view (thl.go): a span that starts before end is counted, so the
# request opens with its line, at its start (thb.eq_refl), covering the
# take of the chat from there (thl.cov: a take opens the list, message by
# message, and holds min(count, length) messages); the first span at or
# past end stops the count, so only turns follow (thl.turns), and that
# span is at or past end (thr.not_lt).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA
import ./thread_history_lines_run.bend as PThreadHistoryLinesRun

# a message is equal to itself
def thl.msg_refl(m: Th.Msg) -> {S.msg_eq(m, m) == True{} : Bool}:
  match m:
    case Th.Msg{+a, +b}:
      LA.thb.and_i(Nat.is_eq(a, a), Nat.is_eq(b, b), LA.thb.eq_refl(a), LA.thb.eq_refl(b))

# the first c messages of d cover d's first c (all of d when it is shorter)
def thl.cov(d: List<&2, Th.Msg>, +c: Nat) -> {S.covers(List.take(&2, Th.Msg, d, c), d, c) == True{} : Bool}:
  match d:
    case Nil{}:
      match c:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case +x <> +dt:
      match c:
        case 0n:
          {==}
        case 1n+k:
          +tk = List.take(&2, Th.Msg, dt, k)
          +p = S.is_prefix(tk, dt)
          +q = Nat.is_eq(List.length(&2, Th.Msg, tk), Nat.min(k, List.length(&2, Th.Msg, dt)))
          +ih = thl.cov(dt, k)
          LA.thb.and_i(Bool.and(S.msg_eq(x, x), p), q, LA.thb.and_i(S.msg_eq(x, x), p, thl.msg_refl(x), LA.thb.and_l(p, q, ih)), LA.thb.and_r(p, q, ih))

# turns hold no view line
def thl.turns(ms: List<&2, Th.Msg>) -> {S.no_lines(Th.turns(ms)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case m <> t:
      thl.turns(t)

def thl.sel_t(b: Bool, -x: Bool, -y: Bool, eb: {b == True{} : Bool}, hx: {x == True{} : Bool}) -> {S.sel(b, x, y) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      LA.thb.absurd_ft({S.sel(False{}, x, y) == True{} : Bool}, eb)

def thl.sel_f(b: Bool, -x: Bool, -y: Bool, eb: {b == False{} : Bool}, hy: {y == True{} : Bool}) -> {S.sel(b, x, y) == True{} : Bool}:
  match b:
    case True{}:
      LA.thb.absurd_tf({S.sel(True{}, x, y) == True{} : Bool}, eb)
    case False{}:
      hy

# the count stopped at a span at or past end: no view line follows
def thl.stop(tail: List<&2, Th.Item>, +st: Nat, +c: Nat, +vt: List<&2, Th.Span>, +ch: List<&2, Th.Msg>, +e: Nat, eb: {Nat.is_lt(st, e) == False{} : Bool}, ht: {S.no_lines(tail) == True{} : Bool}) -> {S.lines_match(Th.Span{st, c} <> vt, ch, e, tail) == True{} : Bool}:
  match tail:
    case Nil{}:
      PThreadHistoryLinesRun.thr.not_lt(st, e, eb)
    case +it <> +rest:
      thl.sel_f(Nat.is_lt(st, e), Bool.and(S.line_ok(ch, Th.Span{st, c}, it), S.lines_match(vt, ch, e, rest)), S.no_lines(it <> rest), eb, ht)

def thl.step(b: Bool, +st: Nat, +c: Nat, +vt: List<&2, Th.Span>, +ch: List<&2, Th.Msg>, +e: Nat, +tail: List<&2, Th.Item>, eb: {Nat.is_lt(st, e) == b : Bool}, +ht: {S.no_lines(tail) == True{} : Bool}, ih: {S.lines_match(vt, ch, e, List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, vt, Th.history_lines.go(Th.starts(vt), e))), tail)) == True{} : Bool}) -> {S.lines_match(Th.Span{st, c} <> vt, ch, e, List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, Th.Span{st, c} <> vt, Th.history_lines.step(b, Th.history_lines.go(Th.starts(vt), e)))), tail)) == True{} : Bool}:
  match b:
    case True{}:
      +d = List.drop(&2, Th.Msg, ch, st)
      +it = {Th.Line{st, List.take(&2, Th.Msg, d, c)} : Th.Item}
      +rest = List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, vt, Th.history_lines.go(Th.starts(vt), e))), tail)
      +ok = LA.thb.and_i(Nat.is_eq(st, st), S.covers(List.take(&2, Th.Msg, d, c), d, c), LA.thb.eq_refl(st), thl.cov(d, c))
      thl.sel_t(Nat.is_lt(st, e), Bool.and(S.line_ok(ch, Th.Span{st, c}, it), S.lines_match(vt, ch, e, rest)), S.no_lines(it <> rest), eb, LA.thb.and_i(S.line_ok(ch, Th.Span{st, c}, it), S.lines_match(vt, ch, e, rest), ok, ih))
    case False{}:
      thl.stop(tail, st, c, vt, ch, e, eb, ht)

def thl.go(view: List<&2, Th.Span>, +ch: List<&2, Th.Msg>, +e: Nat, +tail: List<&2, Th.Item>, +ht: {S.no_lines(tail) == True{} : Bool}) -> {S.lines_match(view, ch, e, List.append(&2, Th.Item, Th.lines(ch, List.take(&2, Th.Span, view, Th.history_lines.go(Th.starts(view), e))), tail)) == True{} : Bool}:
  match view:
    case Nil{}:
      ht
    case sp <> +vt:
      match sp:
        case Th.Span{+st, +c}:
          thl.step(Nat.is_lt(st, e), st, c, vt, ch, e, tail, {==}, ht, thl.go(vt, ch, e, tail, ht))

def Thread.thread_request_lines(s, evs, view, w):
  +lg = Th.log(s, evs)
  +e = Nat.sub(List.length(&2, Th.Msg, lg), w)
  %LA.thb.log_chat(s, evs) : {S.lines_match(view, _, S.end(_, w), Th.request(s, evs, view, w)) == True{} : Bool}
  thl.go(view, lg, e, Th.turns(List.drop(&2, Th.Msg, lg, e)), thl.turns(List.drop(&2, Th.Msg, lg, e)))
