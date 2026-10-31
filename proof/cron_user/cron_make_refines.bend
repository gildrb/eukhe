# eukhe: the proof of LAW cron_make_refines
# A live process's step appends the new job; the last job record of a
# list with one job appended is that job.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_user.bend as CronUser

def mk.last(rs: List<&2, Cr.Rec>, +j: Cr.Job) -> {CronUser.last_job(List.append(&2, Cr.Rec, rs, [Cr.Known{j}])) == Some{j} : Maybe<&2, Cr.Job>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Raw{x}:
          mk.last(t, j)
        case Cr.Known{x}:
          %Equal.sym(Maybe<&2, Cr.Job>, CronUser.last_job(List.append(&2, Cr.Rec, t, [Cr.Known{j}])), Some{j}, mk.last(t, j)) : {CronUser.last_job.pick(_, x) == Some{j} : Maybe<&2, Cr.Job>}
          {==}

def mk.If(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def mk.void(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : mk.If(_, A)
  Unit{}

def mk.alive(b: Bool, +v: Nat, +sc: Cr.Sched, +bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, e: {b == False{} : Bool}) -> {Some{CronUser.made_jv(CronStore.make_spec(Nat.mul(Cr.first(sc, c), 1n+v)))} == CronUser.last_jv(CronUser.last_job(Cr.S.recs(Cr.step.alive(b, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside}))), 1n+v) : Maybe<&2, CronUser.JV>}:
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, Cr.Job>, CronUser.last_job(List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}])), Some{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}, mk.last(rs, Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}})) : {Some{CronUser.made_jv(CronStore.make_spec(Nat.mul(Cr.first(sc, c), 1n+v)))} == CronUser.last_jv(_, 1n+v) : Maybe<&2, CronUser.JV>}
      {==}
    case True{}:
      mk.void({Some{CronUser.made_jv(CronStore.make_spec(Nat.mul(Cr.first(sc, c), 1n+v)))} == CronUser.last_jv(CronUser.last_job(Cr.S.recs(Cr.S{bad, rs, rd, dead, c, n, aside})), 1n+v) : Maybe<&2, CronUser.JV>}, e)

def CronUser.cron_make_refines(v, s, p, sc, alive):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      mk.alive(Cr.has(p, dead), v, sc, bad, rs, rd, dead, c, n, aside, alive)
