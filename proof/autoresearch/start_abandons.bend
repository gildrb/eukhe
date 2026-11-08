# eukhe: the proof of LAW start_abandons

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def sa.rlen(rs: List<&2, ArS.Row>) -> {ArS.rlen(rs) == Autoresearch.ar_count_runs(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      Equal.cong(Nat, Nat, x => 1n+x, ArS.rlen(t), Autoresearch.ar_count_runs(t), sa.rlen(t))

# the shipped count of started runs is the law's
def sa.started(-c: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>) -> {Nat.add(ArS.rlen(runs), ArS.pcount(pend)) == Autoresearch.ar_started(ArS.St{c, seg, mode, runs, pend}) : Nat}:
  match pend:
    case None{}:
      Equal.trans(Nat, Nat.add(ArS.rlen(runs), 0n), ArS.rlen(runs), Autoresearch.ar_count_runs(runs), AS.as.add_zero(ArS.rlen(runs)), sa.rlen(runs))
    case Some{p}:
      Equal.trans(Nat, Nat.add(ArS.rlen(runs), 1n), 1n+ArS.rlen(runs), 1n+Autoresearch.ar_count_runs(runs), AS.as.add_one(ArS.rlen(runs)), Equal.cong(Nat, Nat, x => 1n+x, ArS.rlen(runs), Autoresearch.ar_count_runs(runs), sa.rlen(runs)))

# what an accepted start leaves
def sa.Start(r: ArS.Res, +s: ArS.St, +n: Nat) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {n == 1n+Autoresearch.ar_started(s) : Nat} & {s2 == ArS.St{Autoresearch.ar_cfg(s), Autoresearch.ar_seg(s), Autoresearch.ar_mode(s), ArS.snoc(Autoresearch.ar_runs(s), Autoresearch.ar_gone(s)), Some{ArS.Pend{n, Nil{}, None{}}}} : ArS.St}
    case ArS.Refuse{t}:
      Unit

def sa.at(b: Bool, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, eb: {Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))) == b : Bool})
  -> sa.Start(ArP.begin.at(b, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), c, seg, mode, runs, pend), ArS.St{Some{c}, seg, mode, runs, pend}, n):
  match b:
    case True{}:
      %Equal.sym(Nat, n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), AS.as.nat_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), eb)) : {_ == 1n+Autoresearch.ar_started(ArS.St{Some{c}, seg, mode, runs, pend}) : Nat} & {ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend)), Some{ArS.Pend{1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), Nil{}, None{}}}} == ArS.St{Some{c}, seg, mode, ArS.snoc(runs, Autoresearch.ar_gone(ArS.St{Some{c}, seg, mode, runs, pend})), Some{ArS.Pend{_, Nil{}, None{}}}} : ArS.St}
      %AS.as.gone(Some{c}, seg, mode, runs, pend) : {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) == 1n+Autoresearch.ar_started(ArS.St{Some{c}, seg, mode, runs, pend}) : Nat} & {ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend)), Some{ArS.Pend{1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), Nil{}, None{}}}} == ArS.St{Some{c}, seg, mode, ArS.snoc(runs, _), Some{ArS.Pend{1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), Nil{}, None{}}}} : ArS.St}
      (Equal.cong(Nat, Nat, x => 1n+x, Nat.add(ArS.rlen(runs), ArS.pcount(pend)), Autoresearch.ar_started(ArS.St{Some{c}, seg, mode, runs, pend}), sa.started(Some{c}, seg, mode, runs, pend)), {==})
    case False{}:
      Unit{}

def sa.walk(s: ArS.St, +n: Nat) -> sa.Start(ArP.step(s, ArS.Begin{n}), s, n):
  match s:
    case ArS.St{cfg, +seg, +mode, +runs, +pend}:
      match cfg:
        case None{}:
          Unit{}
        case Some{+c}:
          sa.at(Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))), n, c, seg, mode, runs, pend, {==})

def Autoresearch.start_abandons(s, n, s2, eff, stop, ok):
  %ok : sa.Start(_, s, n)
  sa.walk(s, n)
