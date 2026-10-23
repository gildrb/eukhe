# eukhe: the proof of LAW child_loop_is_a_stall

import Base
import ../../bend/child.bend as Ch
import ../../bend/progress.bend as Pr
import ../../LAWS.bend as Laws
import ../base.bend as L
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
def pp.sames(ps: List<&2, Pr.Peek>) -> List<&2, Ch.Hush>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          Ch.Same{dt} <> pp.sames(rest)

def pp.len_sames(ps: List<&2, Pr.Peek>) -> {List.length(&2, Ch.Hush, pp.sames(ps)) == List.length(&2, Pr.Peek, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          %Equal.sym(Nat, List.length(&2, Ch.Hush, pp.sames(rest)), List.length(&2, Pr.Peek, rest), pp.len_sames(rest)) : {1n+_ == 1n+List.length(&2, Pr.Peek, rest) : Nat}
          {==}

# a watching verdict holds token t
def pp.Keep(x: Ch.Next, +t: Maybe<&2, Nat>) -> Data:
  match x:
    case Ch.Watch{w}:
      {Ch.W.tok(w) == t : Maybe<&2, Nat>}
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
def pp.same_keeps(+cfg: Ch.Cfg, w: Ch.W, +e: Nat) -> pp.Keep(Ch.look(cfg, w, e, Ch.Busy{Ch.W.tok(w)}), Ch.W.tok(w)):
  match w:
    case Ch.W{+tok, +l, +n}:
      %L.pc.moved_self(tok) : pp.Keep(Ch.busy(_, cfg, Ch.W{tok, l, n}, tok, e), tok)
      pp.spend_keeps(Nat.sub(l, e), tok, Ch.Cfg.fails(cfg))

def pp.keep_eq(x: Ch.Next, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}, k: pp.Keep(x, a)) -> pp.Keep(x, b):
  %e : pp.Keep(x, _)
  k

# the watch over the polls of a looping child is the watch over quiet polls
def pp.watch_hush(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next, l: Pr.Loops(ps, hist), +inv: pp.Keep(x, Some{Pr.work(hist)})) -> {Pr.watch(ps, cfg, hist, x) == Ch.hush(pp.sames(ps), cfg, x) : Ch.Next}:
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
              %Equal.sym(Nat, Pr.work(h), Pr.work(hist), same) : {Pr.watch(rest, cfg, h, Ch.look(cfg, v, 1n+dt, Ch.Busy{Some{_}})) == Ch.hush(pp.sames(rest), cfg, Ch.look(cfg, v, 1n+dt, Ch.Busy{Ch.W.tok(v)})) : Ch.Next}
              %inv : {Pr.watch(rest, cfg, h, Ch.look(cfg, v, 1n+dt, Ch.Busy{_})) == Ch.hush(pp.sames(rest), cfg, Ch.look(cfg, v, 1n+dt, Ch.Busy{Ch.W.tok(v)})) : Ch.Next}
              +next = Ch.look(cfg, v, 1n+dt, Ch.Busy{Ch.W.tok(v)})
              +moved = Equal.trans(Maybe<&2, Nat>, Ch.W.tok(v), Some{Pr.work(hist)}, Some{Pr.work(h)}, inv, Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Pr.work(hist), Pr.work(h), Equal.sym(Nat, Pr.work(h), Pr.work(hist), same)))
              pp.watch_hush(rest, cfg, h, next, pp.loops_app(rest, hist, seg, lr), pp.keep_eq(next, Ch.W.tok(v), Some{Pr.work(h)}, moved, pp.same_keeps(cfg, v, 1n+dt)))
            case Ch.Owe{+k}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), Ch.Owe{k}, pp.loops_app(rest, hist, seg, lr), Unit{})
            case Ch.Quiet{}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), Ch.Quiet{}, pp.loops_app(rest, hist, seg, lr), Unit{})

# the bound over the quiet polls the polls are
def pp.long_sames(+w: Ch.W, +ps: List<&2, Pr.Peek>, long: {Nat.is_le(Ch.W.left(w), 1n+List.length(&2, Pr.Peek, ps)) == True{} : Bool}) -> {Nat.is_le(Ch.W.left(w), 1n+List.length(&2, Ch.Hush, pp.sames(ps))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ch.Hush, pp.sames(ps)), List.length(&2, Pr.Peek, ps), pp.len_sames(ps)) : {Nat.is_le(Ch.W.left(w), 1n+_) == True{} : Bool}
  long

def pp.loop_stalls(+cfg: Ch.Cfg, +w: Ch.W, +hist: List<&2, Nat>, p: Pr.Peek, +ps: List<&2, Pr.Peek>, l: Pr.Loops(p <> ps, hist), tok: {Ch.W.tok(w) == Some{Pr.work(hist)} : Maybe<&2, Nat>}, long: {Nat.is_le(Ch.W.left(w), List.length(&2, Pr.Peek, p <> ps)) == True{} : Bool}) -> {Ch.Next.watching(Pr.watch(p <> ps, cfg, hist, Ch.Watch{w})) == False{} : Bool}:
  match p:
    case Pr.Peek{+seg, +dt}:
      +q = {Pr.Peek{seg, dt} : Pr.Peek}
      %Equal.sym(Ch.Next, Pr.watch(q <> ps, cfg, hist, Ch.Watch{w}), Ch.hush(pp.sames(q <> ps), cfg, Ch.Watch{w}), pp.watch_hush(q <> ps, cfg, hist, Ch.Watch{w}, l, tok)) : {Ch.Next.watching(_) == False{} : Bool}
      L.pc.stalls_in_time(cfg, w, Ch.Same{dt}, pp.sames(ps), pp.long_sames(w, ps, long))

def Laws.child_loop_is_a_stall(cfg, w, hist, p, ps, loops, tok, long):
  pp.loop_stalls(cfg, w, hist, p, ps, loops, tok, long)
