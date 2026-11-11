# eukhe: lemmas of the progress term laws (laws/progress_terms.bend)

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ../base/terms.bend as LT
import ../progress/base.bend as LA

# Positions
# ---------

# an act at a position of a list is an act of it
def pgt.in_at(a: List<&2, Nat>, +x: Nat, +b: List<&2, Nat>) -> Pr.In(x, List.append(&2, Nat, a, x <> b)):
  match a:
    case Nil{}:
      Inl{{==}}
    case h <> t:
      Inr{pgt.in_at(t, x, b)}

# mem finds an act at a position of a list
def pgt.mem_at(a: List<&2, Nat>, +x: Nat, +b: List<&2, Nat>) -> {Pr.mem(x, List.append(&2, Nat, a, x <> b)) == True{} : Bool}:
  match a:
    case Nil{}:
      %LT.lt.eq_refl(x) : {Bool.or(_, Pr.mem(x, b)) == True{} : Bool}
      {==}
    case +h <> t:
      LT.lt.or_r(Nat.is_eq(h, x), Pr.mem(x, List.append(&2, Nat, t, x <> b)), pgt.mem_at(t, x, b))

def pgt.only_at.cons(+x: Nat, +h: Nat, -t: List<&2, Nat>, p: ProgressTerms.At(x, t)) -> ProgressTerms.At(x, h <> t):
  (a, r) = p
  (b, e) = r
  (h <> a, (b, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => h <> z, t, List.append(&2, Nat, a, x <> b), e)))

# an act of xs is at a position of xs
def pgt.only_at(+x: Nat, xs: List<&2, Nat>, i: Pr.In(x, xs)) -> ProgressTerms.At(x, xs):
  match xs:
    case Nil{}:
      Empty.absurd(ProgressTerms.At(x, Nil{}), i)
    case +h <> t:
      match i:
        case Inl{eq}:
          (Nil{}, (t, Equal.cong(Nat, List<&2, Nat>, z => z <> t, h, x, Equal.sym(Nat, x, h, eq))))
        case Inr{it}:
          pgt.only_at.cons(x, h, t, pgt.only_at(x, t, it))

# mem holds of an act of xs only
def pgt.mem_in(+x: Nat, xs: List<&2, Nat>, c: {Pr.mem(x, xs) == True{} : Bool}) -> Pr.In(x, xs):
  match xs:
    case Nil{}:
      LT.lt.absurd(Pr.In(x, Nil{}), c)
    case +h <> t:
      LT.lt.or_elim({Nat.is_eq(h, x) == True{} : Bool}, {Pr.mem(x, t) == True{} : Bool}, Pr.In(x, h <> t), LT.lt.or_cases(Nat.is_eq(h, x), Pr.mem(x, t), c), e => Inl{Equal.sym(Nat, h, x, LT.lt.eq_true(h, x, e))}, r => Inr{pgt.mem_in(x, t, r)})

# Runs of acts
# ------------

def pgt.within_split.cons(+h: Nat, -t: List<&2, Nat>, -b: List<&2, Nat>, +s: List<&2, Nat>, i: Pr.In(h, s), p: Pr.Within(t, s) & Pr.Within(b, s)) -> Pr.Within(h <> t, s) & Pr.Within(b, s):
  (r, wb) = p
  ((i, r), wb)

def pgt.within_split(a: List<&2, Nat>, +b: List<&2, Nat>, +s: List<&2, Nat>, w: Pr.Within(List.append(&2, Nat, a, b), s)) -> Pr.Within(a, s) & Pr.Within(b, s):
  match a:
    case Nil{}:
      (Unit{}, w)
    case +h <> t:
      (i, wt) = w
      pgt.within_split.cons(h, t, b, s, i, pgt.within_split(t, b, s, wt))

def pgt.within_join(a: List<&2, Nat>, +b: List<&2, Nat>, +s: List<&2, Nat>, wa: Pr.Within(a, s), wb: Pr.Within(b, s)) -> Pr.Within(List.append(&2, Nat, a, b), s):
  match a:
    case Nil{}:
      wb
    case +h <> t:
      (i, wt) = wa
      (i, pgt.within_join(t, b, s, wt, wb))

def pgt.flat_repeats.cons(-seg: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, +s: List<&2, Nat>, p: Pr.Within(seg, s) & Pr.Within(List.concat(&2, Nat, rest), s), next: Pr.Within(List.concat(&2, Nat, rest), s) -> Pr.Repeats(rest, s)) -> Pr.Repeats(seg <> rest, s):
  (ws, wr) = p
  (ws, next(wr))

def pgt.repeats_flat(segs: List<&2, List<&2, Nat>>, +s: List<&2, Nat>, r: Pr.Repeats(segs, s)) -> Pr.Within(List.concat(&2, Nat, segs), s):
  match segs:
    case Nil{}:
      Unit{}
    case +seg <> +rest:
      (w, rr) = r
      pgt.within_join(seg, List.concat(&2, Nat, rest), s, w, pgt.repeats_flat(rest, s, rr))

def pgt.flat_repeats(segs: List<&2, List<&2, Nat>>, +s: List<&2, Nat>, w: Pr.Within(List.concat(&2, Nat, segs), s)) -> Pr.Repeats(segs, s):
  match segs:
    case Nil{}:
      Unit{}
    case +seg <> +rest:
      pgt.flat_repeats.cons(seg, rest, s, pgt.within_split(seg, List.concat(&2, Nat, rest), s, w), wr => pgt.flat_repeats(rest, s, wr))

def pgt.flat_loops.cons(-seg: List<&2, Nat>, -dt: Nat, -rest: List<&2, Pr.Peek>, +s: List<&2, Nat>, p: Pr.Within(seg, s) & Pr.Within(List.concat(&2, Nat, ProgressTerms.pt_segs(rest)), s), next: Pr.Within(List.concat(&2, Nat, ProgressTerms.pt_segs(rest)), s) -> Pr.Loops(rest, s)) -> Pr.Loops(Pr.Peek{seg, dt} <> rest, s):
  (ws, wr) = p
  (ws, next(wr))

def pgt.loops_flat(ps: List<&2, Pr.Peek>, +s: List<&2, Nat>, l: Pr.Loops(ps, s)) -> Pr.Within(List.concat(&2, Nat, ProgressTerms.pt_segs(ps)), s):
  match ps:
    case Nil{}:
      Unit{}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, dt}:
          (w, rr) = l
          pgt.within_join(seg, List.concat(&2, Nat, ProgressTerms.pt_segs(rest)), s, w, pgt.loops_flat(rest, s, rr))

def pgt.flat_loops(ps: List<&2, Pr.Peek>, +s: List<&2, Nat>, w: Pr.Within(List.concat(&2, Nat, ProgressTerms.pt_segs(ps)), s)) -> Pr.Loops(ps, s):
  match ps:
    case Nil{}:
      Unit{}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, dt}:
          pgt.flat_loops.cons(seg, dt, rest, s, pgt.within_split(seg, List.concat(&2, Nat, ProgressTerms.pt_segs(rest)), s, w), wr => pgt.flat_loops(rest, s, wr))

# The child watch
# ---------------

# a verdict that owes a report stays over any polls
def pgt.watch_owe(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, +k: Ch.Report) -> {Pr.watch(ps, cfg, hist, Ch.Owe{k}) == Ch.Owe{k} : Ch.Next}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Pr.Peek{+seg, dt}:
          pgt.watch_owe(rest, cfg, List.append(&2, Nat, hist, seg), k)

# a quiet verdict stays over any polls
def pgt.watch_quiet(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>) -> {Pr.watch(ps, cfg, hist, Ch.Quiet{}) == Ch.Quiet{} : Ch.Next}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Pr.Peek{+seg, dt}:
          pgt.watch_quiet(rest, cfg, List.append(&2, Nat, hist, seg))

# The goal loop
# -------------

# a stopped goal stays stopped
def pgt.goal_stop(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, +s: Nat) -> {Pr.goal(segs, cap, hist, Pr.Stop{s}) == Pr.Stop{s} : Pr.Goal}:
  match segs:
    case Nil{}:
      {==}
    case seg <> rest:
      {==}

# 1 + n is never at most n
def pgt.succ_le(n: Nat) -> {Nat.is_le(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pgt.succ_le(p)

# acts the session did before are no growth of its work
def pgt.no_growth(+hist: List<&2, Nat>, +seg: List<&2, Nat>, w: Pr.Within(seg, hist)) -> {Pr.grew(hist, seg) == False{} : Bool}:
  %Equal.sym(Nat, Pr.work(List.append(&2, Nat, hist, seg)), Pr.work(hist), LA.pp.repeat(hist, seg, w)) : {Nat.is_le(1n+Pr.work(hist), _) == False{} : Bool}
  pgt.succ_le(Pr.work(hist))

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

def pg.mem(+x: Nat, xs: List<&2, Nat>) -> {ProgressTerms.mem_spec(x, xs) == Pr.mem(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %pg.mem(x, t) : {Bool.or(Nat.is_eq(h, x), ProgressTerms.mem_spec(x, t)) == Bool.or(Nat.is_eq(h, x), _) : Bool}
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
