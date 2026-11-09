# eukhe: the proof of LAW child_loop_is_a_stall

import Base
import ../../bend/child.bend as Ch
import ../../bend/progress.bend as Pr
import ../../spec/child.bend as ChS
import ../../laws/progress.bend as Progress
import ../base/child.bend as LChild
import ./base.bend as LA

def pp.loops_app(ps: List<&2, Pr.Peek>, +hist: List<&2, Nat>, +more: List<&2, Nat>, l: Pr.Loops(ps, hist)) -> Pr.Loops(ps, List.append(&2, Nat, hist, more)):
  match ps:
    case Nil{}:
      Unit{}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          (w, lr) = l
          (LA.pp.within_app(seg, hist, more, w), pp.loops_app(rest, hist, more, lr))

# The subagent watch
# ------------------

# the quiet polls a list of polls is, for bend/child.bend
def pp.sames(ps: List<&2, Pr.Peek>) -> List<&2, ChS.Hush>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          ChS.Same{dt} <> pp.sames(rest)

def pp.len_sames(ps: List<&2, Pr.Peek>) -> {List.length(&2, ChS.Hush, pp.sames(ps)) == List.length(&2, Pr.Peek, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          %Equal.sym(Nat, List.length(&2, ChS.Hush, pp.sames(rest)), List.length(&2, Pr.Peek, rest), pp.len_sames(rest)) : {1n+_ == 1n+List.length(&2, Pr.Peek, rest) : Nat}
          {==}

# a watching verdict holds token t
def pp.Keep(x: Ch.Next, +t: Maybe<&2, Nat>) -> Data:
  match x:
    case Ch.Watch{w}:
      {ChS.held(w) == t : Maybe<&2, Nat>}
    case Ch.Owe{k}:
      Unit
    case Ch.Quiet{}:
      Unit

def pp.spend_keeps(r: Nat, +tok: Maybe<&2, Nat>, +n: Nat) -> pp.Keep(Ch.spend(r, tok, n), tok):
  match r:
    case 0n:
      Unit{}
    case 1n+p:
      {==}

# a poll that reads the token the watch holds keeps it
def pp.same_keeps(+cfg: Ch.Cfg, w: Ch.W, +e: Nat) -> pp.Keep(Ch.look(cfg, w, e, Ch.Busy{ChS.held(w)}), ChS.held(w)):
  match w:
    case Ch.W{+tok, +l, +n}:
      %LChild.pc.moved_self(tok) : pp.Keep(Ch.busy(_, cfg, Ch.W{tok, l, n}, tok, e), tok)
      pp.spend_keeps(Nat.sub(l, e), tok, Ch.Cfg.fails(cfg))

def pp.keep_eq(x: Ch.Next, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}, k: pp.Keep(x, a)) -> pp.Keep(x, b):
  %e : pp.Keep(x, _)
  k

# the watch over the polls of a looping child is the watch over quiet polls
def pp.watch_hush(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next, l: Pr.Loops(ps, hist), +inv: pp.Keep(x, Some{Pr.work(hist)})) -> {Pr.watch(ps, cfg, hist, x) == ChS.hush(pp.sames(ps), cfg, x) : Ch.Next}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          match x:
            case Ch.Watch{+v}:
              (w, lr) = l
              +h = List.append(&2, Nat, hist, seg)
              +same = LA.pp.repeat(hist, seg, w)
              %Equal.sym(Nat, Pr.work(h), Pr.work(hist), same) : {Pr.watch(rest, cfg, h, Ch.look(cfg, v, 1n+dt, Ch.Busy{Some{_}})) == ChS.hush(pp.sames(rest), cfg, Ch.look(cfg, v, 1n+dt, Ch.Busy{ChS.held(v)})) : Ch.Next}
              %inv : {Pr.watch(rest, cfg, h, Ch.look(cfg, v, 1n+dt, Ch.Busy{_})) == ChS.hush(pp.sames(rest), cfg, Ch.look(cfg, v, 1n+dt, Ch.Busy{ChS.held(v)})) : Ch.Next}
              +next = Ch.look(cfg, v, 1n+dt, Ch.Busy{ChS.held(v)})
              +moved = Equal.trans(Maybe<&2, Nat>, ChS.held(v), Some{Pr.work(hist)}, Some{Pr.work(h)}, inv, Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Pr.work(hist), Pr.work(h), Equal.sym(Nat, Pr.work(h), Pr.work(hist), same)))
              pp.watch_hush(rest, cfg, h, next, pp.loops_app(rest, hist, seg, lr), pp.keep_eq(next, ChS.held(v), Some{Pr.work(h)}, moved, pp.same_keeps(cfg, v, 1n+dt)))
            case Ch.Owe{+k}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), Ch.Owe{k}, pp.loops_app(rest, hist, seg, lr), Unit{})
            case Ch.Quiet{}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), Ch.Quiet{}, pp.loops_app(rest, hist, seg, lr), Unit{})

# the bound over the quiet polls the polls are
def pp.long_sames(+l: Nat, +ps: List<&2, Pr.Peek>, long: {Nat.is_le(l, 1n+List.length(&2, Pr.Peek, ps)) == True{} : Bool}) -> {Nat.is_le(l, 1n+List.length(&2, ChS.Hush, pp.sames(ps))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, ChS.Hush, pp.sames(ps)), List.length(&2, Pr.Peek, ps), pp.len_sames(ps)) : {Nat.is_le(l, 1n+_) == True{} : Bool}
  long

def pp.loop_stalls(+cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +hist: List<&2, Nat>, p: Pr.Peek, +ps: List<&2, Pr.Peek>, lo: Pr.Loops(p <> ps, hist), held: {tok == Some{Pr.work(hist)} : Maybe<&2, Nat>}, long: {Nat.is_le(l, List.length(&2, Pr.Peek, p <> ps)) == True{} : Bool}) -> {ChS.watches(Pr.watch(p <> ps, cfg, hist, Ch.Watch{Ch.W{tok, l, n}})) == False{} : Bool}:
  match p:
    case Pr.Peek{+seg, +dt}:
      +q = {Pr.Peek{seg, dt} : Pr.Peek}
      %Equal.sym(Ch.Next, Pr.watch(q <> ps, cfg, hist, Ch.Watch{Ch.W{tok, l, n}}), ChS.hush(pp.sames(q <> ps), cfg, Ch.Watch{Ch.W{tok, l, n}}), pp.watch_hush(q <> ps, cfg, hist, Ch.Watch{Ch.W{tok, l, n}}, lo, held)) : {ChS.watches(_) == False{} : Bool}
      LChild.pc.stalls_in_time(cfg, tok, l, n, ChS.Same{dt}, pp.sames(ps), pp.long_sames(l, ps, long))

def Progress.child_loop_is_a_stall(cfg, tok, l, n, hist, p, ps, loops, held, long):
  pp.loop_stalls(cfg, tok, l, n, hist, p, ps, loops, held, long)
