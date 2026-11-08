# eukhe: the proof of LAW cron_open_refines
# A live process's update steps to a read file; the files moved aside gain
# the corrupt one exactly when there was one (Cr.heal), which is what the
# decision on a corrupt file read for an update (move it aside) does.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/logic.bend as LCfl

def cfo.heal(bad: Maybe<&2, Nat>, +aside: List<&2, Nat>) -> {CronFileView.aside_after(bad, True{}, aside) == Cr.heal(bad, aside) : List<&2, Nat>}:
  match bad:
    case None{}:
      {==}
    case Some{t}:
      {==}

def cfo.get(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def cfo.has(+q: Nat, +p: Nat, +dead: List<&2, Nat>, by: {Some{q} == Some{p} : Maybe<&2, Nat>}, alive: {Cr.has(p, dead) == False{} : Bool}) -> {Cr.has(q, dead) == False{} : Bool}:
  +qp = Equal.cong(Maybe<&2, Nat>, Nat, m => cfo.get(m), Some{q}, Some{p}, by)
  %Equal.sym(Nat, q, p, qp) : {Cr.has(_, dead) == False{} : Bool}
  alive

def cfo.alive(b: Bool, +x: List<&2, Cr.Rec>, +n2: Nat, +bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, e: {b == False{} : Bool}) -> ({CronFileView.aside_after(bad, True{}, aside) == Cr.S.aside(Cr.step.alive(b, Cr.S{None{}, x, rd, dead, c, n2, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})) : List<&2, Nat>} & {Cr.S.bad(Cr.step.alive(b, Cr.S{None{}, x, rd, dead, c, n2, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})) == None{} : Maybe<&2, Nat>}):
  match b:
    case False{}:
      (cfo.heal(bad, aside), {==})
    case True{}:
      LCfl.cfl.absurd(({CronFileView.aside_after(bad, True{}, aside) == Cr.S.aside(Cr.S{bad, rs, rd, dead, c, n, aside}) : List<&2, Nat>} & {Cr.S.bad(Cr.S{bad, rs, rd, dead, c, n, aside}) == None{} : Maybe<&2, Nat>}), e)

def CronFileView.cron_open_refines(s, e, p, by, alive, up):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+q, +sc}:
          cfo.alive(Cr.has(q, dead), List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), 1n+n, bad, rs, rd, dead, c, n, aside, cfo.has(q, p, dead, by, alive))
        case Cr.Take{+q}:
          cfo.alive(Cr.has(q, dead), Cr.recs(Cr.Take{q}, c, dead, rs), n, bad, rs, rd, dead, c, n, aside, cfo.has(q, p, dead, by, alive))
        case Cr.Recover{+q}:
          cfo.alive(Cr.has(q, dead), Cr.recs(Cr.Recover{q}, c, dead, rs), n, bad, rs, rd, dead, c, n, aside, cfo.has(q, p, dead, by, alive))
        case Cr.Finish{+q, +i, +o}:
          cfo.alive(Cr.has(q, dead), Cr.recs(Cr.Finish{q, i, o}, c, dead, rs), n, bad, rs, rd, dead, c, n, aside, cfo.has(q, p, dead, by, alive))
        case Cr.Abort{+q}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Abort{q})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Abort{q})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Die{+q}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Die{q})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Die{q})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Cancel{+q, +i}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Cancel{q, i})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Cancel{q, i})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Resume{+q, +i}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Resume{q, i})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Resume{q, i})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Tick{+d}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Tick{d})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Tick{d})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.RawJob{+t}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.RawJob{t})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.RawJob{t})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.RawClaim{+t}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.RawClaim{t})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.RawClaim{t})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Corrupt{+t}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Corrupt{t})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Corrupt{t})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Pause{+q, +i}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Pause{q, i})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Pause{q, i})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Stop{+q, +i}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Stop{q, i})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Stop{q, i})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Delete{+q, +i}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Delete{q, i})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Delete{q, i})) == None{} : Maybe<&2, Nat>}), up)
        case Cr.Edit{+q, +i, +k}:
          LCfl.cfl.absurdF(({CronFileView.aside_after(bad, CronStore.open_spec(True{}), aside) == Cr.S.aside(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Edit{q, i, k})) : List<&2, Nat>} & {Cr.S.bad(Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Edit{q, i, k})) == None{} : Maybe<&2, Nat>}), up)
