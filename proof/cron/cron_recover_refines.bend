# eukhe: the proof of LAW cron_recover_refines
# A job with no claim stays on both sides. A claim of o on record: the
# laws' verdict from whose it is (p's own: p no longer runs it; another's:
# o is dead) is the model's `clears` for a live p (crv.verdict: when o is p,
# o is not dead); with that verdict both sides clear the claim and end the
# run of an active job alike (crv.go).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore

def tv.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def crv.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tv.If(_, G)
  Unit{}

def crv.eq_of(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      crv.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      crv.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %crv.eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# p's own claim: the verdict clears it exactly when p no longer runs it
def crv.mine(r: Bool, -d: Bool, no: {d == False{} : Bool}) -> {Bool.or(Bool.not(r), d) == CronStore.clear_spec(CS.Mine{r}) : Bool}:
  match r:
    case True{}:
      %Equal.sym(Bool, d, False{}, no) : {Bool.or(False{}, _) == False{} : Bool}
      {==}
    case False{}:
      {==}

def crv.verdict(b: Bool, +p: Nat, +o: Nat, +rs: List<&2, Nat>, +dead: List<&2, Nat>, eq: {Nat.is_eq(o, p) == b : Bool}, alive: {Cr.has(p, dead) == False{} : Bool}) -> {Bool.or(Bool.and(b, Bool.not(Cr.has(p, rs))), Cr.has(o, dead)) == CronStore.clear_spec(Cron.who_of.pick(b, p, o, rs, dead)) : Bool}:
  match b:
    case True{}:
      +op = crv.eq_of(o, p, eq)
      %Equal.sym(Nat, o, p, op) : {Bool.or(Bool.not(Cr.has(p, rs)), Cr.has(_, dead)) == CronStore.clear_spec(CS.Mine{Cr.has(p, rs)}) : Bool}
      crv.mine(Cr.has(p, rs), Cr.has(p, dead), alive)
    case False{}:
      {==}

# with one verdict b, both sides clear the claim, and end the run of an
# active job: a one-shot is finished
def crv.go(b: Bool, +v: Nat, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +oc: Nat, +o: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cron.back_view(CronStore.recover_spec(CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, b), b, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{oc, o}}, rs, ss, h}, 1n+v) == Cron.view(Cr.recover.go(b, i, s, st, nx, k, Cr.Claim{oc, o}, rs, ss, h), 1n+v) : Cron.View()}:
  match b:
    case False{}:
      {==}
    case True{}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}
        case Cr.Every{n}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}

def Cron.cron_recover_refines(v, p, dead, j, alive):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{oc, o}:
              %crv.verdict(Nat.is_eq(o, p), p, o, rs, dead, {==}, alive) : {Cron.back_view(CronStore.recover_spec(CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, _), _, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{oc, o}}, rs, ss, h}, 1n+v) == Cron.view(Cr.recover.go(Cr.clears(p, o, rs, dead), i, s, st, nx, k, Cr.Claim{oc, o}, rs, ss, h), 1n+v) : Cron.View()}
              crv.go(Cr.clears(p, o, rs, dead), v, i, s, st, nx, k, oc, o, rs, ss, h)
