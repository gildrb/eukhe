# eukhe: lemmas of the progress term laws (laws/progress_terms.bend)

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ../lease/base/terms.bend as LT

def pg.mem(+x: Nat, xs: List<&2, Nat>) -> {ProgressTerms.mem_spec(x, xs) == Pr.mem(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %pg.mem(x, t) : {Bool.or(Nat.is_eq(h, x), ProgressTerms.mem_spec(x, t)) == Bool.or(Nat.is_eq(h, x), _) : Bool}
      {==}

def pg.goal(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, g: Pr.Goal) -> {ProgressTerms.goal_spec(segs, cap, hist, g) == Pr.goal(segs, cap, hist, g) : Pr.Goal}:
  match segs:
    case Nil{}:
      {==}
    case +seg <> rest:
      match g:
        case Pr.Go{s}:
          pg.goal(rest, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, Pr.grew(hist, seg)))
        case Pr.Stop{s}:
          {==}

def pg.at(+cfg: Ch.Cfg, +t: Nat, +dt: Nat, x: Ch.Next) -> {ProgressTerms.watch_spec.at(cfg, t, dt, x) == Pr.watch.step(cfg, t, dt, x) : Ch.Next}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      {==}

def pg.watch(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, +x: Ch.Next) -> {ProgressTerms.watch_spec(ps, cfg, hist, x) == Pr.watch(ps, cfg, hist, x) : Ch.Next}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          +now = List.append(&2, Nat, hist, seg)
          %pg.at(cfg, Pr.work(now), dt, x) : {ProgressTerms.watch_spec(rest, cfg, now, ProgressTerms.watch_spec.at(cfg, Pr.work(now), dt, x)) == Pr.watch(rest, cfg, now, _) : Ch.Next}
          pg.watch(rest, cfg, now, ProgressTerms.watch_spec.at(cfg, Pr.work(now), dt, x))

def pg.in_sound(+x: Nat, xs: List<&2, Nat>, i: Pr.In(x, xs)) -> {ProgressTerms.mem_spec(x, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({ProgressTerms.mem_spec(x, Nil{}) == True{} : Bool}, i)
    case +h <> t:
      match i:
        case Inl{eq}:
          %eq : {Bool.or(Nat.is_eq(_, x), ProgressTerms.mem_spec(x, t)) == True{} : Bool}
          %LT.lt.eq_refl(x) : {Bool.or(_, ProgressTerms.mem_spec(x, t)) == True{} : Bool}
          {==}
        case Inr{it}:
          LT.lt.or_r(Nat.is_eq(h, x), ProgressTerms.mem_spec(x, t), pg.in_sound(x, t, it))

def pg.in_complete(+x: Nat, xs: List<&2, Nat>, c: {ProgressTerms.mem_spec(x, xs) == True{} : Bool}) -> Pr.In(x, xs):
  match xs:
    case Nil{}:
      LT.lt.absurd(Pr.In(x, Nil{}), c)
    case +h <> t:
      LT.lt.or_elim({Nat.is_eq(h, x) == True{} : Bool}, {ProgressTerms.mem_spec(x, t) == True{} : Bool}, Pr.In(x, h <> t), LT.lt.or_cases(Nat.is_eq(h, x), ProgressTerms.mem_spec(x, t), c), e => Inl{Equal.sym(Nat, h, x, LT.lt.eq_true(h, x, e))}, r => Inr{pg.in_complete(x, t, r)})

def pg.within_sound(xs: List<&2, Nat>, +s: List<&2, Nat>, d: Pr.Within(xs, s)) -> {ProgressTerms.within_spec(xs, s) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      (i, w) = d
      %Equal.sym(Bool, ProgressTerms.mem_spec(h, s), True{}, pg.in_sound(h, s, i)) : {Bool.and(_, ProgressTerms.within_spec(t, s)) == True{} : Bool}
      pg.within_sound(t, s, w)

def pg.within_complete(xs: List<&2, Nat>, +s: List<&2, Nat>, +c: {ProgressTerms.within_spec(xs, s) == True{} : Bool}) -> Pr.Within(xs, s):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> t:
      (pg.in_complete(h, s, LT.lt.and_l(ProgressTerms.mem_spec(h, s), ProgressTerms.within_spec(t, s), c)), pg.within_complete(t, s, LT.lt.and_r(ProgressTerms.mem_spec(h, s), ProgressTerms.within_spec(t, s), c)))

def pg.repeats_sound(segs: List<&2, List<&2, Nat>>, +s: List<&2, Nat>, d: Pr.Repeats(segs, s)) -> {ProgressTerms.repeats_spec(segs, s) == True{} : Bool}:
  match segs:
    case Nil{}:
      {==}
    case +seg <> rest:
      (w, r) = d
      %Equal.sym(Bool, ProgressTerms.within_spec(seg, s), True{}, pg.within_sound(seg, s, w)) : {Bool.and(_, ProgressTerms.repeats_spec(rest, s)) == True{} : Bool}
      pg.repeats_sound(rest, s, r)

def pg.repeats_complete(segs: List<&2, List<&2, Nat>>, +s: List<&2, Nat>, +c: {ProgressTerms.repeats_spec(segs, s) == True{} : Bool}) -> Pr.Repeats(segs, s):
  match segs:
    case Nil{}:
      Unit{}
    case +seg <> rest:
      (pg.within_complete(seg, s, LT.lt.and_l(ProgressTerms.within_spec(seg, s), ProgressTerms.repeats_spec(rest, s), c)), pg.repeats_complete(rest, s, LT.lt.and_r(ProgressTerms.within_spec(seg, s), ProgressTerms.repeats_spec(rest, s), c)))

def pg.loops_sound(ps: List<&2, Pr.Peek>, +s: List<&2, Nat>, d: Pr.Loops(ps, s)) -> {ProgressTerms.loops_spec(ps, s) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Pr.Peek{+seg, dt}:
          (w, r) = d
          %Equal.sym(Bool, ProgressTerms.within_spec(seg, s), True{}, pg.within_sound(seg, s, w)) : {Bool.and(_, ProgressTerms.loops_spec(rest, s)) == True{} : Bool}
          pg.loops_sound(rest, s, r)

def pg.loops_complete(ps: List<&2, Pr.Peek>, +s: List<&2, Nat>, +c: {ProgressTerms.loops_spec(ps, s) == True{} : Bool}) -> Pr.Loops(ps, s):
  match ps:
    case Nil{}:
      Unit{}
    case p <> rest:
      match p:
        case Pr.Peek{+seg, dt}:
          (pg.within_complete(seg, s, LT.lt.and_l(ProgressTerms.within_spec(seg, s), ProgressTerms.loops_spec(rest, s), c)), pg.loops_complete(rest, s, LT.lt.and_r(ProgressTerms.within_spec(seg, s), ProgressTerms.loops_spec(rest, s), c)))
