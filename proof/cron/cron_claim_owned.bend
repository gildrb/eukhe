# eukhe: the proof of LAW cron_claim_owned

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ./base/bool.bend as LABool
import ./base/cron.bend as LACron
import ./base/nat.bend as LANat

def cron_step.pc.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  LANat.cron.pc.eq_of(a, b, h)

# Claims belong to their owners
# -----------------------------

def pc.MCD(m: Maybe<&2, Cr.Claim>, A: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      A

def pc.none_some_c(-A: Type, -x: Cr.Claim, e: {None{} == Some{x} : Maybe<&2, Cr.Claim>}) -> A:
  %e : pc.MCD(_, A)
  Unit{}

def pc.owner_of(m: Maybe<&2, Cr.Claim>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case Cr.Claim{q, w}:
          w

# what a step may do to the claim of o on a job
def pc.CK(+e: Cr.Ev, +dead: List<&2, Nat>, j2: Cr.Job, +x: Nat, +o: Nat) -> Type:
  Or({Cr.Job.claim(j2) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool}))

def pc.cl_take_due(b: Bool, cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Nat, +o: Nat, hc: {cl == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> {Cr.Job.claim(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}:
  match b:
    case False{}:
      hc
    case True{}:
      match cl:
        case None{}:
          pc.none_some_c({Cr.Job.claim(Cr.take.due(True{}, p, c, i, s, n, k, None{}, rs, ss, h)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Cr.Claim{x, o}, hc)
        case Some{y}:
          hc

def pc.cl_take(+p: Nat, +c: Nat, j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> {Cr.Job.claim(Cr.take(p, c, j)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}:
  match j:
    case Cr.Job{+i, +s, st, nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              hc
            case Some{+n}:
              pc.cl_take_due(Nat.is_le(n, c), cl, p, c, i, s, n, k, rs, ss, h, x, o, hc)
        case Cr.Paused{}:
          hc
        case Cr.Finished{}:
          hc
        case Cr.Cancelled{}:
          hc

def pc.why2(a: Bool, -b: Bool, -d: Bool, +o: Nat, +p: Nat, -dead: List<&2, Nat>, ea: {Nat.is_eq(o, p) == a : Bool}, ed: {Cr.has(o, dead) == d : Bool}, h: {Bool.or(Bool.and(a, Bool.not(b)), d) == True{} : Bool}) -> Or({o == p : Nat}, {Cr.has(o, dead) == True{} : Bool}):
  match a:
    case True{}:
      Inl{cron_step.pc.eq_of(o, p, ea)}
    case False{}:
      Inr{Equal.trans(Bool, Cr.has(o, dead), d, True{}, ed, h)}

# a claim a recovery clears is its own, or a dead process's
def pc.clears_why(+p: Nat, +o: Nat, +rs: List<&2, Nat>, +dead: List<&2, Nat>, h: {Cr.clears(p, o, rs, dead) == True{} : Bool}) -> Or({o == p : Nat}, {Cr.has(o, dead) == True{} : Bool}):
  pc.why2(Nat.is_eq(o, p), Cr.has(p, rs), Cr.has(o, dead), o, p, dead, {==}, {==}, h)

def pc.by_from(+p: Nat, +o2: Nat, +o: Nat, +dead: List<&2, Nat>, eo: {o2 == o : Nat}, w: Or({o2 == p : Nat}, {Cr.has(o2, dead) == True{} : Bool})) -> Or({Some{p} == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool}):
  match w:
    case Inl{e}:
      +po = Equal.trans(Nat, p, o2, o, Equal.sym(Nat, o2, p, e), eo)
      Inl{Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, p, o, po)}
    case Inr{d}:
      %eo : Or({Some{p} == Some{_} : Maybe<&2, Nat>}, {Cr.has(_, dead) == True{} : Bool})
      Inr{d}

def pc.cl_rec_go(b: Bool, +st: Cr.Status, +p: Nat, +o2: Nat, +xo: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Nat, +o: Nat, eq: {Cr.clears(p, o2, rs, dead) == b : Bool}, hc: {Some{Cr.Claim{xo, o2}} == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(Cr.Recover{p}, dead, Cr.recover.go(b, i, s, st, nx, k, Cr.Claim{xo, o2}, rs, ss, h), x, o):
  match b:
    case False{}:
      Inl{hc}
    case True{}:
      +eo = Equal.cong(Maybe<&2, Cr.Claim>, Nat, m => pc.owner_of(m), Some{Cr.Claim{xo, o2}}, Some{Cr.Claim{x, o}}, hc)
      Inr{pc.by_from(p, o2, o, dead, eo, pc.clears_why(p, o2, rs, dead, eq))}

def pc.cl_recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(Cr.Recover{p}, dead, Cr.recover(p, dead, j), x, o):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          pc.none_some_c(pc.CK(Cr.Recover{p}, dead, Cr.recover(p, dead, Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}), x, o), Cr.Claim{x, o}, hc)
        case Some{y}:
          match y:
            case Cr.Claim{+xo, +o2}:
              pc.cl_rec_go(Cr.clears(p, o2, rs, dead), st, p, o2, xo, dead, i, s, nx, k, rs, ss, h, x, o, {==}, hc)

def pc.cl_own(b: Bool, +w: Nat, +xo: Nat, +p: Nat, +c: Nat, +out: Cr.Out, +dead: List<&2, Nat>, +ji: Nat, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Nat, +o: Nat, eqb: {Nat.is_eq(w, p) == b : Bool}, hc: {Some{Cr.Claim{xo, w}} == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(Cr.Finish{p, ji, out}, dead, Cr.finish.own(b, Cr.Claim{xo, w}, c, out, i, s, st, nx, k, rs, ss, h), x, o):
  match b:
    case False{}:
      Inl{hc}
    case True{}:
      +wo = Equal.cong(Maybe<&2, Cr.Claim>, Nat, m => pc.owner_of(m), Some{Cr.Claim{xo, w}}, Some{Cr.Claim{x, o}}, hc)
      +po = Equal.trans(Nat, p, w, o, Equal.sym(Nat, w, p, cron_step.pc.eq_of(w, p, eqb)), wo)
      Inr{Inl{Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, p, o, po)}}

def pc.cl_run(b: Bool, cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +out: Cr.Out, +dead: List<&2, Nat>, +ji: Nat, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Nat, +o: Nat, hc: {cl == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(Cr.Finish{p, ji, out}, dead, Cr.finish.run(b, p, c, out, i, s, st, nx, k, cl, rs, ss, h), x, o):
  match b:
    case False{}:
      Inl{hc}
    case True{}:
      match cl:
        case None{}:
          pc.none_some_c(pc.CK(Cr.Finish{p, ji, out}, dead, Cr.finish.run(True{}, p, c, out, i, s, st, nx, k, None{}, rs, ss, h), x, o), Cr.Claim{x, o}, hc)
        case Some{y}:
          match y:
            case Cr.Claim{+xo, +w}:
              pc.cl_own(Nat.is_eq(w, p), w, xo, p, c, out, dead, ji, i, s, st, nx, k, Cr.drop(p, rs), ss, h, x, o, {==}, hc)

def pc.cl_finish(b: Bool, +p: Nat, +c: Nat, +out: Cr.Out, +dead: List<&2, Nat>, +ji: Nat, +j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(Cr.Finish{p, ji, out}, dead, Cr.job.pick(b, Cr.finish(p, c, out, j), j), x, o):
  match b:
    case False{}:
      Inl{hc}
    case True{}:
      match j:
        case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
          pc.cl_run(Cr.has(p, rs), cl, p, c, out, dead, ji, i, s, st, nx, k, rs, ss, h, x, o, hc)

def pc.cl_cancel(b: Bool, j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> {Cr.Job.claim(Cr.job.pick(b, Cr.cancel(j), j)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}:
  match b:
    case False{}:
      hc
    case True{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          match st:
            case Cr.Cancelled{}:
              hc
            case Cr.Active{}:
              hc
            case Cr.Paused{}:
              hc
            case Cr.Finished{}:
              hc

def pc.cl_resume(b: Bool, +c: Nat, j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> {Cr.Job.claim(Cr.job.pick(b, Cr.resume(c, j), j)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}:
  match b:
    case False{}:
      hc
    case True{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          match s:
            case Cr.Once{d}:
              hc
            case Cr.Every{q}:
              match st:
                case Cr.Active{}:
                  hc
                case Cr.Paused{}:
                  hc
                case Cr.Finished{}:
                  hc
                case Cr.Cancelled{}:
                  hc

def pc.cl_unrun(+p: Nat, j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> {Cr.Job.claim(Cr.unrun(p, j)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      hc

def pc.claim_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +x: Nat, +o: Nat, hc: {Cr.Job.claim(j) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CK(e, dead, Cr.job(e, c, dead, j), x, o):
  match e:
    case Cr.Take{+p}:
      Inl{pc.cl_take(p, c, j, x, o, hc)}
    case Cr.Recover{+p}:
      pc.cl_recover(p, dead, j, x, o, hc)
    case Cr.Finish{+p, +ji, +out}:
      pc.cl_finish(Nat.is_eq(Cr.Job.id(j), ji), p, c, out, dead, ji, j, x, o, hc)
    case Cr.Abort{+p}:
      Inl{pc.cl_unrun(p, j, x, o, hc)}
    case Cr.Die{+p}:
      Inl{pc.cl_unrun(p, j, x, o, hc)}
    case Cr.Cancel{+p, +ji}:
      Inl{pc.cl_cancel(Nat.is_eq(Cr.Job.id(j), ji), j, x, o, hc)}
    case Cr.Resume{+p, +ji}:
      Inl{pc.cl_resume(Nat.is_eq(Cr.Job.id(j), ji), c, j, x, o, hc)}
    case Cr.Create{p, s}:
      Inl{hc}
    case Cr.Tick{d}:
      Inl{hc}
    case Cr.RawJob{t}:
      Inl{hc}
    case Cr.RawClaim{t}:
      Inl{hc}
    case Cr.Corrupt{t}:
      Inl{hc}

# the claim of o on job i after e on the records
def pc.CR(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +i: Nat, +x: Nat, +o: Nat) -> Type:
  Or({Cr.claim_of(i, Cr.recs(e, c, dead, rs)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool}))

def pc.claim_pick(b: Bool, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +rest: List<&2, Cr.Rec>, +i: Nat, +x: Nat, +o: Nat, h: {Cr.claim_of.pick(b, Cr.Job.claim(j), Cr.claim_of(i, rest)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, next: {Cr.claim_of(i, rest) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> pc.CR(e, c, dead, rest, i, x, o)) -> Or({Cr.claim_of.pick(b, Cr.Job.claim(Cr.job(e, c, dead, j)), Cr.claim_of(i, Cr.recs(e, c, dead, rest))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool})):
  match b:
    case True{}:
      pc.claim_job(e, c, dead, j, x, o, h)
    case False{}:
      next(h)

def pc.claim_rec(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +i: Nat, +x: Nat, +o: Nat, h: {Cr.claim_of(i, rs) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CR(e, c, dead, rs, i, x, o):
  match rs:
    case Nil{}:
      pc.none_some_c(pc.CR(e, c, dead, Nil{}, i, x, o), Cr.Claim{x, o}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{y}:
          pc.claim_rec(e, c, dead, rest, i, x, o, h)
        case Cr.Known{+j}:
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), LACron.pc.id_job(e, c, dead, j)) : Or({Cr.claim_of.pick(Nat.is_eq(_, i), Cr.Job.claim(Cr.job(e, c, dead, j)), Cr.claim_of(i, Cr.recs(e, c, dead, rest))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool}))
          pc.claim_pick(Nat.is_eq(Cr.Job.id(j), i), e, c, dead, j, rest, i, x, o, h, q => pc.claim_rec(e, c, dead, rest, i, x, o, q))

def pc.claim_pick_app(b: Bool, +j: Cr.Job, +rest: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, -m: Maybe<&2, Cr.Claim>, h: {Cr.claim_of.pick(b, Cr.Job.claim(j), Cr.claim_of(i, rest)) == m : Maybe<&2, Cr.Claim>}, next: {Cr.claim_of(i, rest) == m : Maybe<&2, Cr.Claim>} -> {Cr.claim_of(i, List.append(&2, Cr.Rec, rest, ys)) == m : Maybe<&2, Cr.Claim>}) -> {Cr.claim_of.pick(b, Cr.Job.claim(j), Cr.claim_of(i, List.append(&2, Cr.Rec, rest, ys))) == m : Maybe<&2, Cr.Claim>}:
  match b:
    case True{}:
      h
    case False{}:
      next(h)

def pc.claim_append(rs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, +y: Cr.Claim, h: {Cr.claim_of(i, rs) == Some{y} : Maybe<&2, Cr.Claim>}) -> {Cr.claim_of(i, List.append(&2, Cr.Rec, rs, ys)) == Some{y} : Maybe<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      pc.none_some_c({Cr.claim_of(i, ys) == Some{y} : Maybe<&2, Cr.Claim>}, y, h)
    case r <> +rest:
      match r:
        case Cr.Raw{z}:
          pc.claim_append(rest, ys, i, y, h)
        case Cr.Known{+j}:
          pc.claim_pick_app(Nat.is_eq(Cr.Job.id(j), i), j, rest, ys, i, Some{y}, h, q => pc.claim_append(rest, ys, i, y, q))

# the claim step law: a step of p removes a claim of o only when o is p or
# dead
def pc.CO(+s: Cr.S, +s2: Cr.S, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat) -> Type:
  Or({Cr.claim_of(i, Cr.S.recs(s2)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool}))

def pc.co_alive(b: Bool, +s: Cr.S, +a: Cr.S, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat, h: {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, ka: pc.CO(s, a, e, i, x, o)) -> pc.CO(s, Cr.step.alive(b, a, s), e, i, x, o):
  match b:
    case False{}:
      ka
    case True{}:
      Inl{h}

def pc.co_raw(bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +rd2: List<&2, Nat>, +ys: List<&2, Cr.Rec>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat, h: {Cr.claim_of(i, rs) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CO(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, ys), rd2, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}), e, i, x, o):
  match bad:
    case None{}:
      Inl{pc.claim_append(rs, ys, i, Cr.Claim{x, o}, h)}
    case Some{z}:
      Inl{h}

def pc.co_raw_claim(bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +t: Nat, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat, h: {Cr.claim_of(i, rs) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CO(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}), e, i, x, o):
  match bad:
    case None{}:
      Inl{h}
    case Some{z}:
      Inl{h}

def pc.claim_owned(s: Cr.S, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat, nc: {Cr.Ev.is_corrupt(e) == False{} : Bool}, +h: {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}) -> pc.CO(s, Cr.step(s, e), e, i, x, o):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          +new = {[Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}] : List<&2, Cr.Rec>}
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, List.append(&2, Cr.Rec, rs, new), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, e, i, x, o, h, Inl{pc.claim_append(rs, new, i, Cr.Claim{x, o}, h)})
        case Cr.Take{+p}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Recover{+p}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Finish{+p, +ji, +out}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Abort{+p}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Die{+p}:
          pc.claim_rec(e, c, dead, rs, i, x, o, h)
        case Cr.Cancel{+p, +ji}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Resume{+p, +ji}:
          pc.co_alive(Cr.has(p, dead), Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, e, i, x, o, h, pc.claim_rec(e, c, dead, rs, i, x, o, h))
        case Cr.Tick{+d}:
          Inl{h}
        case Cr.RawJob{+t}:
          pc.co_raw(bad, rs, rd, rd, [Cr.Raw{t}], dead, c, n, aside, e, i, x, o, h)
        case Cr.RawClaim{+t}:
          pc.co_raw_claim(bad, rs, rd, t, dead, c, n, aside, e, i, x, o, h)
        case Cr.Corrupt{t}:
          LABool.cron_step.pc.absurd(pc.CO(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{Some{t}, Nil{}, Nil{}, dead, c, n, aside}, e, i, x, o), nc)

def pc.cron_claim_owned(+s: Cr.S, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat) -> {Cr.Ev.is_corrupt(e) == False{} : Bool} -> {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> Or({Cr.claim_of(i, Cr.S.recs(Cr.step(s, e))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool})):
  nc => h => pc.claim_owned(s, e, i, x, o, nc, h)

def Cron.cron_claim_owned(s, e, i, x, o):
  pc.cron_claim_owned(s, e, i, x, o)
