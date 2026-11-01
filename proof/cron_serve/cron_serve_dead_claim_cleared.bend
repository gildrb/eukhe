# eukhe: the proof of LAW cron_serve_dead_claim_cleared
# A recovery answers each claim record with the verdict on it (a drop when
# the claim is cleared). The verdict on a claim that does not stay clears
# it: this process's own claim of a dispatch it does not run, another's
# claim whose owner is dead.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx
import ./base/logic.bend as LG

def dc.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def dc.some_inj(-A: Data, a: A, b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  %e : {a == dc.val(A, a, _) : A}
  {==}

def dc.isn(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def dc.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : dc.isn(A, _, G)
  Unit{}

# a recovery answers each claim record with the verdict on it
def dc.rec_at(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>, k: Nat, +c: Sv.CRec, at: {List.get(&2, Sv.CRec, cs, k) == Some{c} : Maybe<&2, Sv.CRec>}) -> {List.get(&2, Sv.COut, Sv.recover.claims(me, runs, dead, cs), k) == Some{Sv.recover.claim(Sv.clears(me, runs, dead, c))} : Maybe<&2, Sv.COut>}:
  match cs k:
    case Nil{} _:
      dc.none_some(Sv.CRec, c, {List.get(&2, Sv.COut, Nil{}, k) == Some{Sv.recover.claim(Sv.clears(me, runs, dead, c))} : Maybe<&2, Sv.COut>}, at)
    case +h <> t 0n:
      +e = dc.some_inj(Sv.CRec, h, c, at)
      %e : {Some{Sv.recover.claim(Sv.clears(me, runs, dead, h))} == Some{Sv.recover.claim(Sv.clears(me, runs, dead, _))} : Maybe<&2, Sv.COut>}
      {==}
    case h <> t 1n+p:
      dc.rec_at(me, runs, dead, t, p, c, at)

def dc.not_f(+b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LG.lg.tf({False{} == True{} : Bool}, h)

# the verdict on a claim that does not stay clears it
def dc.gone.own(own: Bool, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +d: String, +o: Nat, gone: {CronServe.sv_stays.own(own, CronServe.sv_in(d, runs), Bool.not(CronServe.sv_has(o, dead))) == False{} : Bool}) -> {Sv.recover.claim(CS.clear(Sv.who(own, d, o, runs, dead))) == Sv.CDrop{} : Sv.COut}:
  match own:
    case True{}:
      %Equal.sym(Bool, Sv.has_str(d, runs), CronServe.sv_in(d, runs), LSx.sx.in(d, runs)) : {Sv.recover.claim(Bool.not(_)) == Sv.CDrop{} : Sv.COut}
      %Equal.sym(Bool, CronServe.sv_in(d, runs), False{}, gone) : {Sv.recover.claim(Bool.not(_)) == Sv.CDrop{} : Sv.COut}
      {==}
    case False{}:
      %Equal.sym(Bool, Cr.has(o, dead), CronServe.sv_has(o, dead), LSx.sx.has(o, dead)) : {Sv.recover.claim(_) == Sv.CDrop{} : Sv.COut}
      %Equal.sym(Bool, CronServe.sv_has(o, dead), True{}, dc.not_f(CronServe.sv_has(o, dead), gone)) : {Sv.recover.claim(_) == Sv.CDrop{} : Sv.COut}
      {==}

def CronServe.cron_serve_dead_claim_cleared(runs, me, js, cs, dead, k, d, j, o, at, gone):
  Equal.trans(Maybe<&2, Sv.COut>, List.get(&2, Sv.COut, Sv.recover.claims(me, runs, dead, cs), k), Some{Sv.recover.claim(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}))}, Some{Sv.CDrop{}}, dc.rec_at(me, runs, dead, cs, k, Sv.CKnown{d, j, o}, at), Equal.cong(Sv.COut, Maybe<&2, Sv.COut>, v => Some{v}, Sv.recover.claim(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o})), Sv.CDrop{}, dc.gone.own(Nat.is_eq(o, me), me, runs, dead, d, o, gone)))
