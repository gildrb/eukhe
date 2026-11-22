# eukhe: the proof of LAW auto_stops_without_progress

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

# Numbers
# -------

def pp.lt_self(+n: Nat) -> {Nat.is_le(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pp.lt_self(p)

def pp.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, pp.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def pp.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pp.add_succ(p, b)) : {1n+_ == 2n+Nat.add(p, b) : Nat}
      {==}

def pp.repeats_app(segs: List<&2, List<&2, Nat>>, +hist: List<&2, Nat>, +more: List<&2, Nat>, r: Pr.Repeats(segs, hist)) -> Pr.Repeats(segs, List.append(&2, Nat, hist, more)):
  match segs:
    case Nil{}:
      Unit{}
    case +seg <> +rest:
      (w, rr) = r
      (LA.pp.within_app(seg, hist, more, w), pp.repeats_app(rest, hist, more, rr))

# The run's progress check
# ------------------------

# a run of repeats does not grow the work
def pp.grew_no(+hist: List<&2, Nat>, +seg: List<&2, Nat>, w: Pr.Within(seg, hist)) -> {Pr.grew(hist, seg) == False{} : Bool}:
  %Equal.sym(Nat, Pr.work(List.append(&2, Nat, hist, seg)), Pr.work(hist), LA.pp.repeat(hist, seg, w)) : {Nat.is_le(1n+Pr.work(hist), _) == False{} : Bool}
  pp.lt_self(Pr.work(hist))

# the last check: the stalls reach twice the cap, so the run stops
def pp.last.at(b: Bool, steer: Bool, +c2: Nat, +cap: Nat, +s: Nat, +h: List<&2, Nat>, e: {Nat.is_le(c2, 1n+s) == b : Bool}, long: {Nat.is_le(c2, 1n+s) == True{} : Bool}) -> {Pr.Run.stopped(Pr.run(Nil{}, cap, h, Pr.strike.put(b, steer, 1n+s))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.pp.absurdT({Pr.Run.stopped(Pr.run(Nil{}, cap, h, Pr.strike.go(steer, 1n+s))) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(c2, 1n+s), False{}, Equal.sym(Bool, Nat.is_le(c2, 1n+s), True{}, long), e))

# a steered run goes on like one that goes on
def pp.next.go(steer: Bool, +cap: Nat, +s: Nat, +h: List<&2, Nat>, +seg: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, ih: {Pr.Run.stopped(Pr.run(seg <> rest, cap, h, Pr.Go{1n+s})) == True{} : Bool}) -> {Pr.Run.stopped(Pr.run(seg <> rest, cap, h, Pr.strike.go(steer, 1n+s))) == True{} : Bool}:
  match steer:
    case True{}:
      ih
    case False{}:
      ih

# a check before the last: the run stops now, or the next checks stop it
def pp.next.at(b: Bool, steer: Bool, +cap: Nat, +s: Nat, +h: List<&2, Nat>, +seg: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, ih: {Pr.Run.stopped(Pr.run(seg <> rest, cap, h, Pr.Go{1n+s})) == True{} : Bool}) -> {Pr.Run.stopped(Pr.run(seg <> rest, cap, h, Pr.strike.put(b, steer, 1n+s))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pp.next.go(steer, cap, s, h, seg, rest, ih)

# the bound at the last check
def pp.long_last(+c2: Nat, +s: Nat, long: {Nat.is_le(c2, Nat.add(1n+s, 0n)) == True{} : Bool}) -> {Nat.is_le(c2, 1n+s) == True{} : Bool}:
  %pp.add_zero(1n+s) : {Nat.is_le(c2, _) == True{} : Bool}
  long

# the bound after one more check
def pp.long_next(+c2: Nat, +s: Nat, +l: Nat, long: {Nat.is_le(c2, Nat.add(1n+s, 1n+l)) == True{} : Bool}) -> {Nat.is_le(c2, Nat.add(2n+s, l)) == True{} : Bool}:
  %pp.add_succ(s, l) : {Nat.is_le(c2, 1n+_) == True{} : Bool}
  long

# from Go{s}, checks of repeats stop the run once s + their number
# reaches twice the cap
def pp.stops(rest: List<&2, List<&2, Nat>>, +seg: List<&2, Nat>, +cap: Nat, +s: Nat, +hist: List<&2, Nat>, r: Pr.Repeats(seg <> rest, hist), long: {Nat.is_le(Nat.add(cap, cap), Nat.add(1n+s, List.length(&2, List<&2, Nat>, rest))) == True{} : Bool}) -> {Pr.Run.stopped(Pr.run(seg <> rest, cap, hist, Pr.Go{s})) == True{} : Bool}:
  match rest:
    case Nil{}:
      (w, rr) = r
      %Equal.sym(Bool, Pr.grew(hist, seg), False{}, pp.grew_no(hist, seg, w)) : {Pr.Run.stopped(Pr.run(Nil{}, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _))) == True{} : Bool}
      pp.last.at(Nat.is_le(Nat.add(cap, cap), 1n+s), Nat.is_eq(cap, 1n+s), Nat.add(cap, cap), cap, s, List.append(&2, Nat, hist, seg), {==}, pp.long_last(Nat.add(cap, cap), s, long))
    case +seg2 <> +rest2:
      (w, rr) = r
      +h = List.append(&2, Nat, hist, seg)
      %Equal.sym(Bool, Pr.grew(hist, seg), False{}, pp.grew_no(hist, seg, w)) : {Pr.Run.stopped(Pr.run(seg2 <> rest2, cap, h, Pr.check(cap, s, _))) == True{} : Bool}
      pp.next.at(Nat.is_le(Nat.add(cap, cap), 1n+s), Nat.is_eq(cap, 1n+s), cap, s, h, seg2, rest2, pp.stops(rest2, seg2, cap, 1n+s, h, pp.repeats_app(seg2 <> rest2, hist, seg, rr), pp.long_next(Nat.add(cap, cap), s, List.length(&2, List<&2, Nat>, rest2), long)))

def pp.run_stops(+cap: Nat, +s: Nat, +hist: List<&2, Nat>, +seg: List<&2, Nat>, +segs: List<&2, List<&2, Nat>>, r: Pr.Repeats(seg <> segs, hist), long: {Nat.is_le(Nat.add(cap, cap), List.length(&2, List<&2, Nat>, seg <> segs)) == True{} : Bool}) -> {Pr.Run.stopped(Pr.run(seg <> segs, cap, hist, Pr.Go{s})) == True{} : Bool}:
  +l = List.length(&2, List<&2, Nat>, segs)
  pp.stops(segs, seg, cap, s, hist, r, LNat.child.pc.le_trans(Nat.add(cap, cap), 1n+l, Nat.add(1n+s, l), long, LNat.child.pc.le_add(s, l)))

# a stopped verdict is Stop with its count
def pp.stop_of(g: Pr.Run, e: {Pr.Run.stopped(g) == True{} : Bool}) -> {g == Pr.Stop{Pr.Run.stalls(g)} : Pr.Run}:
  match g:
    case Pr.Go{n}:
      LA.pp.absurdT({Pr.Go{n} == Pr.Stop{n} : Pr.Run}, Equal.sym(Bool, False{}, True{}, e))
    case Pr.Stop{n}:
      {==}
    case Pr.Steer{n}:
      LA.pp.absurdT({Pr.Steer{n} == Pr.Stop{n} : Pr.Run}, Equal.sym(Bool, False{}, True{}, e))

def Progress.auto_stops_without_progress(cap, s, hist, seg, segs, repeats, long):
  +g = Pr.run(seg <> segs, cap, hist, Pr.Go{s})
  (Pr.Run.stalls(g), pp.stop_of(g, pp.run_stops(cap, s, hist, seg, segs, repeats, long)))
