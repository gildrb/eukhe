# proof_cron_step: the cron laws of laws/cron.bend (D2) about one step from
# any state (bend/cron.bend): no step but the file's corruption drops a
# record (`cron_never_drops`); a step of p removes the claim of o only when
# o is p or dead (`cron_claim_owned`); a paused job stays paused through
# every step that is not a user action, and the failure backoff never
# shrinks (the rest of `cron_backoff_bounded`). The invariant laws are in
# bend/proof_cron.bend.

import Base
import ./cron.bend as Cr
import ./proof_cron.bend as Pc

# Logic, from bend/proof_cron.bend
# --------------------------------

def pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  Pc.pc.absurd(A, e)

def pc.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Pc.pc.absurdF(A, e)

def pc.void(-A: Type, e: Empty) -> A:
  Pc.pc.void(A, e)

def pc.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  Pc.pc.eq_refl(k)

def pc.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  Pc.pc.eq_of(a, b, h)

def pc.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  Pc.pc.or_l(a, b, h)

def pc.or_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  Pc.pc.or_r(a, b, h)

def pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  Pc.pc.le_refl(n)

# Ids stay
# --------

def pc.id_take_due(b: Bool, +p: Nat, +c: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          {==}

def pc.id_take(+p: Nat, +c: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.take(p, c, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, st, nx, +k, cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+n}:
              pc.id_take_due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_rec_go(b: Bool, st: Cr.Status, +s: Cr.Sched, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.recover.go(b, i, s, st, nx, k, x, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{q}:
              {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> {Cr.Job.id(Cr.recover(p, dead, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+xo, +o}:
              pc.id_rec_go(Cr.clears(p, o, rs, dead), st, s, i, nx, k, Cr.Claim{xo, o}, rs, ss, h)

def pc.id_fail(b: Bool, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.fail(b, c, i, s, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.id_count(b: Bool, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.count(b, c, o, i, s, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      match o:
        case Cr.Win{}:
          {==}
        case Cr.Skip{}:
          {==}
        case Cr.Loss{}:
          pc.id_fail(Nat.is_lt(1n+k, Cr.CAP()), c, i, s, nx, 1n+k, rs, ss, Cr.MLoss{} <> h)

def pc.id_own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.own(b, x, c, o, i, s, st, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          pc.id_count(Cr.is_once(s), c, o, i, s, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_run(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+xo, +w}:
              pc.id_own(Nat.is_eq(w, p), Cr.Claim{xo, w}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)

def pc.id_finish(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job) -> {Cr.Job.id(Cr.finish(p, c, o, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      pc.id_run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)

def pc.id_cancel(j: Cr.Job) -> {Cr.Job.id(Cr.cancel(j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Cancelled{}:
          {==}
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}

def pc.id_resume(+c: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.resume(c, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          {==}
        case Cr.Every{q}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}

def pc.id_unrun(+p: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.unrun(p, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def pc.id_pick(b: Bool, a: Cr.Job, +j: Cr.Job, ea: {Cr.Job.id(a) == Cr.Job.id(j) : Nat}) -> {Cr.Job.id(Cr.job.pick(b, a, j)) == Cr.Job.id(j) : Nat}:
  match b:
    case True{}:
      ea
    case False{}:
      {==}

def pc.id_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job) -> {Cr.Job.id(Cr.job(e, c, dead, j)) == Cr.Job.id(j) : Nat}:
  match e:
    case Cr.Take{+p}:
      pc.id_take(p, c, j)
    case Cr.Recover{+p}:
      pc.id_recover(p, dead, j)
    case Cr.Finish{+p, +i, +o}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.finish(p, c, o, j), j, pc.id_finish(p, c, o, j))
    case Cr.Abort{+p}:
      pc.id_unrun(p, j)
    case Cr.Die{+p}:
      pc.id_unrun(p, j)
    case Cr.Cancel{+p, +i}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.cancel(j), j, pc.id_cancel(j))
    case Cr.Resume{+p, +i}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.resume(c, j), j, pc.id_resume(c, j))
    case Cr.Create{p, s}:
      {==}
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}

# Nothing is dropped
# ------------------

def pc.or_mono(a: Bool, b: Bool, -b2: Bool, h: {Bool.or(a, b) == True{} : Bool}, f: {b == True{} : Bool} -> {b2 == True{} : Bool}) -> {Bool.or(a, b2) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def pc.raw_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +t: Nat, h: {Cr.has_raw(t, rs) == True{} : Bool}) -> {Cr.has_raw(t, Cr.recs(e, c, dead, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h
    case r <> +rest:
      match r:
        case Cr.Raw{+x}:
          pc.or_mono(Nat.is_eq(x, t), Cr.has_raw(t, rest), Cr.has_raw(t, Cr.recs(e, c, dead, rest)), h, q => pc.raw_recs(e, c, dead, rest, t, q))
        case Cr.Known{j}:
          pc.raw_recs(e, c, dead, rest, t, h)

def pc.raw_append(rs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +t: Nat, h: {Cr.has_raw(t, rs) == True{} : Bool}) -> {Cr.has_raw(t, List.append(&2, Cr.Rec, rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      pc.absurdF({Cr.has_raw(t, ys) == True{} : Bool}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{+x}:
          pc.or_mono(Nat.is_eq(x, t), Cr.has_raw(t, rest), Cr.has_raw(t, List.append(&2, Cr.Rec, rest, ys)), h, q => pc.raw_append(rest, ys, t, q))
        case Cr.Known{j}:
          pc.raw_append(rest, ys, t, h)

def pc.job_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +i: Nat, h: {Cr.has_job(i, rs) == True{} : Bool}) -> {Cr.has_job(i, Cr.recs(e, c, dead, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h
    case r <> +rest:
      match r:
        case Cr.Raw{x}:
          pc.job_recs(e, c, dead, rest, i, h)
        case Cr.Known{+j}:
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), pc.id_job(e, c, dead, j)) : {Bool.or(Nat.is_eq(_, i), Cr.has_job(i, Cr.recs(e, c, dead, rest))) == True{} : Bool}
          pc.or_mono(Nat.is_eq(Cr.Job.id(j), i), Cr.has_job(i, rest), Cr.has_job(i, Cr.recs(e, c, dead, rest)), h, q => pc.job_recs(e, c, dead, rest, i, q))

def pc.job_append(rs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, h: {Cr.has_job(i, rs) == True{} : Bool}) -> {Cr.has_job(i, List.append(&2, Cr.Rec, rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      pc.absurdF({Cr.has_job(i, ys) == True{} : Bool}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{x}:
          pc.job_append(rest, ys, i, h)
        case Cr.Known{+j}:
          pc.or_mono(Nat.is_eq(Cr.Job.id(j), i), Cr.has_job(i, rest), Cr.has_job(i, List.append(&2, Cr.Rec, rest, ys)), h, q => pc.job_append(rest, ys, i, q))

def pc.has_append(xs: List<&2, Nat>, +ys: List<&2, Nat>, +t: Nat, h: {Cr.has(t, xs) == True{} : Bool}) -> {Cr.has(t, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      pc.absurdF({Cr.has(t, ys) == True{} : Bool}, h)
    case +x <> +rest:
      pc.or_mono(Nat.is_eq(x, t), Cr.has(t, rest), Cr.has(t, List.append(&2, Nat, rest, ys)), h, q => pc.has_append(rest, ys, t, q))

def pc.ND(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def pc.none_some_t(-t: Nat, h: {None{} == Some{t} : Maybe<&2, Nat>}) -> Empty:
  %h : pc.ND(_)
  Unit{}

def pc.MDP(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

# the corrupt file t is moved aside
def pc.heal_has(bad: Maybe<&2, Nat>, +t: Nat, +aside: List<&2, Nat>, h: {bad == Some{t} : Maybe<&2, Nat>}) -> {Cr.has(t, Cr.heal(bad, aside)) == True{} : Bool}:
  match bad:
    case None{}:
      pc.void({Cr.has(t, aside) == True{} : Bool}, pc.none_some_t(t, h))
    case Some{+x}:
      +xt = Equal.cong(Maybe<&2, Nat>, Nat, m => pc.MDP(m), Some{x}, Some{t}, h)
      %Equal.sym(Nat, x, t, xt) : {Bool.or(Nat.is_eq(_, t), Cr.has(t, aside)) == True{} : Bool}
      pc.or_l(Nat.is_eq(t, t), Cr.has(t, aside), pc.eq_refl(t))

def pc.heal_keep(bad: Maybe<&2, Nat>, +t: Nat, +aside: List<&2, Nat>, h: {Cr.has(t, aside) == True{} : Bool}) -> {Cr.has(t, Cr.heal(bad, aside)) == True{} : Bool}:
  match bad:
    case None{}:
      h
    case Some{+x}:
      pc.or_r(Nat.is_eq(x, t), Cr.has(t, aside), h)

def pc.keeps_refl(+t: Nat, +i: Nat, +s: Cr.S) -> Cr.Keeps(t, i, s, s):
  (h => h, (h => h, (h => h, (h => Inl{h}, h => h))))

def pc.keeps_alive(b: Bool, +t: Nat, +i: Nat, +s: Cr.S, +a: Cr.S, ka: Cr.Keeps(t, i, s, a)) -> Cr.Keeps(t, i, s, Cr.step.alive(b, a, s)):
  match b:
    case False{}:
      ka
    case True{}:
      pc.keeps_refl(t, i, s)

def pc.keeps_raw_job(bad: Maybe<&2, Nat>, +x: Nat, +t: Nat, +i: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>) -> Cr.Keeps(t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{x}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      (h => pc.raw_append(rs, [Cr.Raw{x}], t, h), (h => pc.job_append(rs, [Cr.Raw{x}], i, h), (h => h, (h => pc.void(Or({None{} == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, aside) == True{} : Bool}), pc.none_some_t(t, h)), h => h))))
    case Some{+y}:
      pc.keeps_refl(t, i, Cr.S{Some{y}, rs, rd, dead, c, n, aside})

def pc.keeps_raw_claim(bad: Maybe<&2, Nat>, +x: Nat, +t: Nat, +i: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>) -> Cr.Keeps(t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [x]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      (h => h, (h => h, (h => pc.has_append(rd, [x], t, h), (h => pc.void(Or({None{} == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, aside) == True{} : Bool}), pc.none_some_t(t, h)), h => h))))
    case Some{+y}:
      pc.keeps_refl(t, i, Cr.S{Some{y}, rs, rd, dead, c, n, aside})

def pc.never_drops(s: Cr.S, +e: Cr.Ev, +t: Nat, +i: Nat, nc: {Cr.Ev.is_corrupt(e) == False{} : Bool}) -> Cr.Keeps(t, i, s, Cr.step(s, e)):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          +new = {[Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}] : List<&2, Cr.Rec>}
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, List.append(&2, Cr.Rec, rs, new), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, (h => pc.raw_append(rs, new, t, h), (h => pc.job_append(rs, new, i, h), (h => h, (h => Inr{pc.heal_has(bad, t, aside, h)}, h => pc.heal_keep(bad, t, aside, h))))))
        case Cr.Take{+p}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inr{pc.heal_has(bad, t, aside, h)}, h => pc.heal_keep(bad, t, aside, h))))))
        case Cr.Recover{+p}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inr{pc.heal_has(bad, t, aside, h)}, h => pc.heal_keep(bad, t, aside, h))))))
        case Cr.Finish{+p, +ji, +o}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inr{pc.heal_has(bad, t, aside, h)}, h => pc.heal_keep(bad, t, aside, h))))))
        case Cr.Abort{+p}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inl{h}, h => h)))))
        case Cr.Die{+p}:
          (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inl{h}, h => h))))
        case Cr.Cancel{+p, +ji}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inl{h}, h => h)))))
        case Cr.Resume{+p, +ji}:
          pc.keeps_alive(Cr.has(p, dead), t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside}, (h => pc.raw_recs(e, c, dead, rs, t, h), (h => pc.job_recs(e, c, dead, rs, i, h), (h => h, (h => Inl{h}, h => h)))))
        case Cr.Tick{+d}:
          (h => h, (h => h, (h => h, (h => Inl{h}, h => h))))
        case Cr.RawJob{+x}:
          pc.keeps_raw_job(bad, x, t, i, rs, rd, dead, c, n, aside)
        case Cr.RawClaim{+x}:
          pc.keeps_raw_claim(bad, x, t, i, rs, rd, dead, c, n, aside)
        case Cr.Corrupt{x}:
          pc.absurd(Cr.Keeps(t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{Some{x}, Nil{}, Nil{}, dead, c, n, aside}), nc)

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
      Inl{pc.eq_of(o, p, ea)}
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
      +po = Equal.trans(Nat, p, w, o, Equal.sym(Nat, w, p, pc.eq_of(w, p, eqb)), wo)
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
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), pc.id_job(e, c, dead, j)) : Or({Cr.claim_of.pick(Nat.is_eq(_, i), Cr.Job.claim(Cr.job(e, c, dead, j)), Cr.claim_of(i, Cr.recs(e, c, dead, rest))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, dead) == True{} : Bool}))
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
          pc.absurd(pc.CO(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{Some{t}, Nil{}, Nil{}, dead, c, n, aside}, e, i, x, o), nc)

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
      pc.absurd(pc.PSJ(Cr.job(Cr.Cancel{p, ji}, c, dead, j)), nu)
    case Cr.Resume{+p, +ji}:
      pc.absurd(pc.PSJ(Cr.job(Cr.Resume{p, ji}, c, dead, j)), nu)
    case Cr.Create{+p, +sc}:
      pc.absurd(pc.PSJ(Cr.job(Cr.Create{p, sc}, c, dead, j)), nu)
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
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), pc.id_job(e, c, dead, j)) : {Cr.status_of.pick(Nat.is_eq(_, i), Cr.Job.status(Cr.job(e, c, dead, j)), Cr.status_of(i, Cr.recs(e, c, dead, rest))) == pc.SP() : Maybe<&2, Cr.Status>}
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
          pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Create{p, sc})), nu)
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
          pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Cancel{p, ji})), nu)
        case Cr.Resume{+p, +ji}:
          pc.absurd(pc.SPO(i, Cr.step(Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.Resume{p, ji})), nu)
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
      pc.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pc.not_lt_le(p, q, h)

def pc.ge_pick(b: Bool, +n: Nat, +u: Nat, eq: {Nat.is_lt(n, u) == b : Bool}) -> {Nat.is_le(u, Cr.later.pick(b, n, u)) == True{} : Bool}:
  match b:
    case True{}:
      pc.le_refl(u)
    case False{}:
      pc.not_lt_le(n, u, eq)

# a failure never moves the next run before its pause ends
def pc.later_ge(nx: Maybe<&2, Nat>, +u: Nat) -> {Nat.is_le(u, Cr.later(nx, u)) == True{} : Bool}:
  match nx:
    case None{}:
      pc.le_refl(u)
    case Some{+n}:
      pc.ge_pick(Nat.is_lt(n, u), n, u, {==})

# The laws
# --------

def pc.cron_fires_once(+evs: List<&2, Cr.Ev>) -> Cr.FiresAll(Cr.S.recs(Cr.run(evs))):
  Pc.pc.fires_of(Cr.run(evs), Pc.pc.inv_run(evs))

def pc.cron_once_finished_after_end(+evs: List<&2, Cr.Ev>) -> Cr.EndsAll(Cr.S.recs(Cr.run(evs))):
  Pc.pc.ends_of(Cr.run(evs), Pc.pc.inv_run(evs))

def pc.cron_never_drops(+s: Cr.S, +e: Cr.Ev, +t: Nat, +i: Nat) -> {Cr.Ev.is_corrupt(e) == False{} : Bool} -> Cr.Keeps(t, i, s, Cr.step(s, e)):
  nc => pc.never_drops(s, e, t, i, nc)

def pc.cron_claim_owned(+s: Cr.S, +e: Cr.Ev, +i: Nat, +x: Nat, +o: Nat) -> {Cr.Ev.is_corrupt(e) == False{} : Bool} -> {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> Or({Cr.claim_of(i, Cr.S.recs(Cr.step(s, e))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool})):
  nc => h => pc.claim_owned(s, e, i, x, o, nc, h)

def pc.cron_backoff_bounded(+evs: List<&2, Cr.Ev>, +s: Cr.S, +e: Cr.Ev, +i: Nat, +k: Nat, +c: Nat, +nx: Maybe<&2, Nat>) -> (Cr.StopsAll(Cr.S.recs(Cr.run(evs))) & (({Cr.Ev.is_user(e) == False{} : Bool} -> Cr.StaysPaused(i, s, Cr.step(s, e))) & ({Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool} & {Nat.is_le(Nat.add(c, Cr.delay(k)), Cr.later(nx, Nat.add(c, Cr.delay(k)))) == True{} : Bool}))):
  (Pc.pc.stops_of(Cr.run(evs), Pc.pc.inv_run(evs)), (nu => h => pc.stays(s, e, i, nu, h), (pc.delay_mono(k), pc.later_ge(nx, Nat.add(c, Cr.delay(k))))))
