# eukhe: the proof of LAW cron_backoff_bounded

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ./base/cron.bend as LACron
import ./base/logic.bend as LALogic
import ./base/nat.bend as LANat

def cron.pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cron.pc.le_refl(p)

def pc.stops_st(st: Cr.Status, +k: Nat, +h: List<&2, Cr.Mark>, ek: {k == Cr.trail(h) : Nat}, +act: LALogic.pc.Act2(st, k)) -> ({Nat.is_le(Cr.trail(h), Cr.CAP()) == True{} : Bool} & Cr.Act(st, Cr.trail(h))):
  match st:
    case Cr.Active{}:
      %ek : ({Nat.is_le(_, Cr.CAP()) == True{} : Bool} & Cr.Act(Cr.Active{}, _))
      (LANat.pc.lt_le(k, Cr.CAP(), act), act)
    case Cr.Paused{}:
      %ek : ({Nat.is_le(_, Cr.CAP()) == True{} : Bool} & Unit)
      (act, Unit{})
    case Cr.Finished{}:
      %ek : ({Nat.is_le(_, Cr.CAP()) == True{} : Bool} & Unit)
      (act, Unit{})
    case Cr.Cancelled{}:
      %ek : ({Nat.is_le(_, Cr.CAP()) == True{} : Bool} & Unit)
      (act, Unit{})

def pc.g_stops(+c: Nat, +dead: List<&2, Nat>, j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> Cr.Stops(j):
  match j:
    case Cr.Job{i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (ek, act) = h6
      pc.stops_st(st, k, h, ek, act)

def pc.all_stops(+c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, g: LALogic.pc.AllG(c, dead, rs)) -> Cr.StopsAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_stops(c, dead, j, a), pc.all_stops(c, dead, t, b))
        case Cr.Raw{x}:
          pc.all_stops(c, dead, t, g)

def pc.stops_of(s: Cr.S, inv: LALogic.pc.Inv(s)) -> Cr.StopsAll(Cr.S.recs(s)):
  match s:
    case Cr.S{b, rs, rd, +dead, +c, n, a}:
      pc.all_stops(c, dead, rs, inv)

def cron_step.pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  cron.pc.le_refl(n)

# A stopped job stays stopped
# ---------------------------

def pc.PSJ(j: Cr.Job) -> Data:
  {Cr.Job.status(j) == Cr.Paused{} : Cr.Status}

def pc.SDA(st: Cr.Status, A: Type) -> Type:
  match st:
    case Cr.Paused{}:
      A
    case Cr.Active{}:
      Unit
    case Cr.Finished{}:
      Unit
    case Cr.Cancelled{}:
      Unit

# a status other than paused is not paused
def pc.st_absurd(-A: Type, -st: Cr.Status, e: {st == Cr.Paused{} : Cr.Status}, u: pc.SDA(st, A)) -> A:
  %e : pc.SDA(_, A)
  u

def pc.st_take(+p: Nat, +c: Nat, j: Cr.Job, hp: pc.PSJ(j)) -> pc.PSJ(Cr.take(p, c, j)):
  match j:
    case Cr.Job{+i, +s, st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Paused{}:
          {==}
        case Cr.Active{}:
          pc.st_absurd(pc.PSJ(Cr.take(p, c, Cr.Job{i, s, Cr.Active{}, nx, k, cl, rs, ss, h})), Cr.Active{}, hp, Unit{})
        case Cr.Finished{}:
          pc.st_absurd(pc.PSJ(Cr.take(p, c, Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h})), Cr.Finished{}, hp, Unit{})
        case Cr.Cancelled{}:
          pc.st_absurd(pc.PSJ(Cr.take(p, c, Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h})), Cr.Cancelled{}, hp, Unit{})

def pc.st_rec_go(b: Bool, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> pc.PSJ(Cr.recover.go(b, i, s, Cr.Paused{}, nx, k, x, rs, ss, h)):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pc.st_recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job, hp: pc.PSJ(j)) -> pc.PSJ(Cr.recover(p, dead, j)):
  match j:
    case Cr.Job{+i, +s, st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Paused{}:
          match cl:
            case None{}:
              {==}
            case Some{y}:
              match y:
                case Cr.Claim{+xo, +o}:
                  pc.st_rec_go(Cr.clears(p, o, rs, dead), i, s, nx, k, Cr.Claim{xo, o}, rs, ss, h)
        case Cr.Active{}:
          pc.st_absurd(pc.PSJ(Cr.recover(p, dead, Cr.Job{i, s, Cr.Active{}, nx, k, cl, rs, ss, h})), Cr.Active{}, hp, Unit{})
        case Cr.Finished{}:
          pc.st_absurd(pc.PSJ(Cr.recover(p, dead, Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h})), Cr.Finished{}, hp, Unit{})
        case Cr.Cancelled{}:
          pc.st_absurd(pc.PSJ(Cr.recover(p, dead, Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h})), Cr.Cancelled{}, hp, Unit{})

def pc.st_own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> pc.PSJ(Cr.finish.own(b, x, c, o, i, s, Cr.Paused{}, nx, k, rs, ss, h)):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pc.st_run(b: Bool, cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> pc.PSJ(Cr.finish.run(b, p, c, o, i, s, Cr.Paused{}, nx, k, cl, rs, ss, h)):
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{y}:
          match y:
            case Cr.Claim{+xo, +w}:
              pc.st_own(Nat.is_eq(w, p), Cr.Claim{xo, w}, c, o, i, s, nx, k, Cr.drop(p, rs), ss, h)

def pc.st_finish(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job, hp: pc.PSJ(j)) -> pc.PSJ(Cr.finish(p, c, o, j)):
  match j:
    case Cr.Job{+i, +s, st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Paused{}:
          pc.st_run(Cr.has(p, rs), cl, p, c, o, i, s, nx, k, rs, ss, h)
        case Cr.Active{}:
          pc.st_absurd(pc.PSJ(Cr.finish(p, c, o, Cr.Job{i, s, Cr.Active{}, nx, k, cl, rs, ss, h})), Cr.Active{}, hp, Unit{})
        case Cr.Finished{}:
          pc.st_absurd(pc.PSJ(Cr.finish(p, c, o, Cr.Job{i, s, Cr.Finished{}, nx, k, cl, rs, ss, h})), Cr.Finished{}, hp, Unit{})
        case Cr.Cancelled{}:
          pc.st_absurd(pc.PSJ(Cr.finish(p, c, o, Cr.Job{i, s, Cr.Cancelled{}, nx, k, cl, rs, ss, h})), Cr.Cancelled{}, hp, Unit{})

def pc.st_pick_fin(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +j: Cr.Job, +hp: pc.PSJ(j)) -> pc.PSJ(Cr.job.pick(b, Cr.finish(p, c, o, j), j)):
  match b:
    case True{}:
      pc.st_finish(p, c, o, j, hp)
    case False{}:
      hp

def pc.st_unrun(+p: Nat, j: Cr.Job, hp: pc.PSJ(j)) -> pc.PSJ(Cr.unrun(p, j)):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      hp

def pc.paused_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, nu: {Cr.Ev.is_user(e) == False{} : Bool}, +hp: pc.PSJ(j)) -> pc.PSJ(Cr.job(e, c, dead, j)):
  match e:
    case Cr.Take{+p}:
      pc.st_take(p, c, j, hp)
    case Cr.Recover{+p}:
      pc.st_recover(p, dead, j, hp)
    case Cr.Finish{+p, +ji, +o}:
      pc.st_pick_fin(Nat.is_eq(Cr.Job.id(j), ji), p, c, o, j, hp)
    case Cr.Abort{+p}:
      pc.st_unrun(p, j, hp)
    case Cr.Die{+p}:
      pc.st_unrun(p, j, hp)
    case Cr.Cancel{+p, +ji}:
      LALogic.cron_step.pc.absurd(pc.PSJ(Cr.job(Cr.Cancel{p, ji}, c, dead, j)), nu)
    case Cr.Resume{+p, +ji}:
      LALogic.cron_step.pc.absurd(pc.PSJ(Cr.job(Cr.Resume{p, ji}, c, dead, j)), nu)
    case Cr.Create{+p, +sc}:
      LALogic.cron_step.pc.absurd(pc.PSJ(Cr.job(Cr.Create{p, sc}, c, dead, j)), nu)
    case Cr.Tick{d}:
      hp
    case Cr.RawJob{t}:
      hp
    case Cr.RawClaim{t}:
      hp
    case Cr.Corrupt{t}:
      hp

def pc.MS(m: Maybe<&2, Cr.Status>) -> Cr.Status:
  match m:
    case None{}:
      Cr.Active{}
    case Some{x}:
      x

def pc.MSD(m: Maybe<&2, Cr.Status>, A: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      A

def pc.none_some_s(-A: Type, e: {None{} == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}) -> A:
  %e : pc.MSD(_, A)
  Unit{}

def pc.SP() -> Maybe<&2, Cr.Status>:
  Some{Cr.Paused{}}

def pc.status_pick(b: Bool, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +rest: List<&2, Cr.Rec>, +i: Nat, nu: {Cr.Ev.is_user(e) == False{} : Bool}, h: {Cr.status_of.pick(b, Cr.Job.status(j), Cr.status_of(i, rest)) == pc.SP() : Maybe<&2, Cr.Status>}, next: {Cr.status_of(i, rest) == pc.SP() : Maybe<&2, Cr.Status>} -> {Cr.status_of(i, Cr.recs(e, c, dead, rest)) == pc.SP() : Maybe<&2, Cr.Status>}) -> {Cr.status_of.pick(b, Cr.Job.status(Cr.job(e, c, dead, j)), Cr.status_of(i, Cr.recs(e, c, dead, rest))) == pc.SP() : Maybe<&2, Cr.Status>}:
  match b:
    case True{}:
      +hp = Equal.cong(Maybe<&2, Cr.Status>, Cr.Status, m => pc.MS(m), Some{Cr.Job.status(j)}, Some{Cr.Paused{}}, h)
      Equal.cong(Cr.Status, Maybe<&2, Cr.Status>, v => Some{v}, Cr.Job.status(Cr.job(e, c, dead, j)), Cr.Paused{}, pc.paused_job(e, c, dead, j, nu, hp))
    case False{}:
      next(h)

def pc.status_rec(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +i: Nat, +nu: {Cr.Ev.is_user(e) == False{} : Bool}, h: {Cr.status_of(i, rs) == pc.SP() : Maybe<&2, Cr.Status>}) -> {Cr.status_of(i, Cr.recs(e, c, dead, rs)) == pc.SP() : Maybe<&2, Cr.Status>}:
  match rs:
    case Nil{}:
      pc.none_some_s({Cr.status_of(i, Nil{}) == pc.SP() : Maybe<&2, Cr.Status>}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{y}:
          pc.status_rec(e, c, dead, rest, i, nu, h)
        case Cr.Known{+j}:
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), LACron.pc.id_job(e, c, dead, j)) : {Cr.status_of.pick(Nat.is_eq(_, i), Cr.Job.status(Cr.job(e, c, dead, j)), Cr.status_of(i, Cr.recs(e, c, dead, rest))) == pc.SP() : Maybe<&2, Cr.Status>}
          pc.status_pick(Nat.is_eq(Cr.Job.id(j), i), e, c, dead, j, rest, i, nu, h, q => pc.status_rec(e, c, dead, rest, i, nu, q))

def pc.status_pick_app(b: Bool, +st: Cr.Status, +rest: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, h: {Cr.status_of.pick(b, st, Cr.status_of(i, rest)) == pc.SP() : Maybe<&2, Cr.Status>}, next: {Cr.status_of(i, rest) == pc.SP() : Maybe<&2, Cr.Status>} -> {Cr.status_of(i, List.append(&2, Cr.Rec, rest, ys)) == pc.SP() : Maybe<&2, Cr.Status>}) -> {Cr.status_of.pick(b, st, Cr.status_of(i, List.append(&2, Cr.Rec, rest, ys))) == pc.SP() : Maybe<&2, Cr.Status>}:
  match b:
    case True{}:
      h
    case False{}:
      next(h)

def pc.status_append(rs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, h: {Cr.status_of(i, rs) == pc.SP() : Maybe<&2, Cr.Status>}) -> {Cr.status_of(i, List.append(&2, Cr.Rec, rs, ys)) == pc.SP() : Maybe<&2, Cr.Status>}:
  match rs:
    case Nil{}:
      pc.none_some_s({Cr.status_of(i, ys) == pc.SP() : Maybe<&2, Cr.Status>}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{z}:
          pc.status_append(rest, ys, i, h)
        case Cr.Known{+j}:
          pc.status_pick_app(Nat.is_eq(Cr.Job.id(j), i), Cr.Job.status(j), rest, ys, i, h, q => pc.status_append(rest, ys, i, q))

# what the law asks of the records after a step
def pc.SPO(+i: Nat, +s2: Cr.S) -> Type:
  Or({Cr.status_of(i, Cr.S.recs(s2)) == pc.SP() : Maybe<&2, Cr.Status>}, {Cr.status_of(i, Cr.S.recs(s2)) == None{} : Maybe<&2, Cr.Status>})

def pc.sp_alive(b: Bool, +i: Nat, +s: Cr.S, +a: Cr.S, h: {Cr.status_of(i, Cr.S.recs(s)) == pc.SP() : Maybe<&2, Cr.Status>}, ka: pc.SPO(i, a)) -> pc.SPO(i, Cr.step.alive(b, a, s)):
  match b:
    case False{}:
      ka
    case True{}:
      Inl{h}

def pc.sp_raw(bad: Maybe<&2, Nat>, +i: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +t: Nat, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, h: {Cr.status_of(i, rs) == pc.SP() : Maybe<&2, Cr.Status>}) -> pc.SPO(i, Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      Inl{pc.status_append(rs, [Cr.Raw{t}], i, h)}
    case Some{z}:
      Inl{h}

def pc.sp_raw_claim(bad: Maybe<&2, Nat>, +i: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +t: Nat, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, h: {Cr.status_of(i, rs) == pc.SP() : Maybe<&2, Cr.Status>}) -> pc.SPO(i, Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      Inl{h}
    case Some{z}:
      Inl{h}

def pc.stays(s: Cr.S, +e: Cr.Ev, +i: Nat, +nu: {Cr.Ev.is_user(e) == False{} : Bool}, +h: {Cr.status_of(i, Cr.S.recs(s)) == pc.SP() : Maybe<&2, Cr.Status>}) -> pc.SPO(i, Cr.step(s, e)):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          LALogic.cron_step.pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Create{p, sc})), nu)
        case Cr.Take{+p}:
          pc.sp_alive(Cr.has(p, dead), i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, h, Inl{pc.status_rec(e, c, dead, rs, i, nu, h)})
        case Cr.Recover{+p}:
          pc.sp_alive(Cr.has(p, dead), i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, h, Inl{pc.status_rec(e, c, dead, rs, i, nu, h)})
        case Cr.Finish{+p, +ji, +o}:
          pc.sp_alive(Cr.has(p, dead), i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, h, Inl{pc.status_rec(e, c, dead, rs, i, nu, h)})
        case Cr.Abort{+p}:
          pc.sp_alive(Cr.has(p, dead), i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, h, Inl{pc.status_rec(e, c, dead, rs, i, nu, h)})
        case Cr.Die{+p}:
          Inl{pc.status_rec(e, c, dead, rs, i, nu, h)}
        case Cr.Cancel{+p, +ji}:
          LALogic.cron_step.pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Cancel{p, ji})), nu)
        case Cr.Resume{+p, +ji}:
          LALogic.cron_step.pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Resume{p, ji})), nu)
        case Cr.Tick{+d}:
          Inl{h}
        case Cr.RawJob{+t}:
          pc.sp_raw(bad, i, rs, rd, t, dead, c, n, aside, h)
        case Cr.RawClaim{+t}:
          pc.sp_raw_claim(bad, i, rs, rd, t, dead, c, n, aside, h)
        case Cr.Corrupt{t}:
          Inr{{==}}

# The pause never shrinks
# -----------------------

def pc.delay_mono(k: Nat) -> {Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+d:
              match d:
                case 0n:
                  {==}
                case 1n+e:
                  match e:
                    case 0n:
                      {==}
                    case 1n+f:
                      match f:
                        case 0n:
                          {==}
                        case 1n+g:
                          {==}

def pc.not_lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LALogic.cron_step.pc.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pc.not_lt_le(p, q, h)

def pc.ge_pick(b: Bool, +n: Nat, +u: Nat, eq: {Nat.is_lt(n, u) == b : Bool}) -> {Nat.is_le(u, Cr.later.pick(b, n, u)) == True{} : Bool}:
  match b:
    case True{}:
      cron_step.pc.le_refl(u)
    case False{}:
      pc.not_lt_le(n, u, eq)

# a failure never moves the next run before its pause ends
def pc.later_ge(nx: Maybe<&2, Nat>, +u: Nat) -> {Nat.is_le(u, Cr.later(nx, u)) == True{} : Bool}:
  match nx:
    case None{}:
      cron_step.pc.le_refl(u)
    case Some{+n}:
      pc.ge_pick(Nat.is_lt(n, u), n, u, {==})

def pc.cron_backoff_bounded(+evs: List<&2, Cr.Ev>, +s: Cr.S, +e: Cr.Ev, +i: Nat, +k: Nat, +c: Nat, +nx: Maybe<&2, Nat>) -> (Cr.StopsAll(Cr.S.recs(Cr.run(evs))) & (({Cr.Ev.is_user(e) == False{} : Bool} -> Cr.StaysPaused(i, s, Cr.step(s, e))) & ({Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool} & {Nat.is_le(Nat.add(c, Cr.delay(k)), Cr.later(nx, Nat.add(c, Cr.delay(k)))) == True{} : Bool}))):
  (pc.stops_of(Cr.run(evs), LACron.pc.inv_run(evs)), (nu => h => pc.stays(s, e, i, nu, h), (pc.delay_mono(k), pc.later_ge(nx, Nat.add(c, Cr.delay(k))))))

def Cron.cron_backoff_bounded(evs, s, e, i, k, c, nx):
  pc.cron_backoff_bounded(evs, s, e, i, k, c, nx)
