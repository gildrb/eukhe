# eukhe: the proof of LAW cron_never_drops

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ./base/bool.bend as LABool
import ./base/cron.bend as LACron
import ./base/logic.bend as LALogic
import ./base/nat.bend as LANat

def cron.pc.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LABool.cron.pc.absurdF({Bool.or(False{}, b) == True{} : Bool}, h)

def cron.pc.or_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def cron_step.pc.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  LABool.cron.pc.absurdF(A, e)

def cron_step.pc.void(-A: Type, e: Empty) -> A:
  LALogic.cron.pc.void(A, e)

def cron_step.pc.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  LANat.cron.pc.eq_refl(k)

def cron_step.pc.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  cron.pc.or_l(a, b, h)

def cron_step.pc.or_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  cron.pc.or_r(a, b, h)

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
      cron_step.pc.absurdF({Cr.has_raw(t, ys) == True{} : Bool}, h)
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
          %Equal.sym(Nat, Cr.Job.id(Cr.job(e, c, dead, j)), Cr.Job.id(j), LACron.pc.id_job(e, c, dead, j)) : {Bool.or(Nat.is_eq(_, i), Cr.has_job(i, Cr.recs(e, c, dead, rest))) == True{} : Bool}
          pc.or_mono(Nat.is_eq(Cr.Job.id(j), i), Cr.has_job(i, rest), Cr.has_job(i, Cr.recs(e, c, dead, rest)), h, q => pc.job_recs(e, c, dead, rest, i, q))

def pc.job_append(rs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, +i: Nat, h: {Cr.has_job(i, rs) == True{} : Bool}) -> {Cr.has_job(i, List.append(&2, Cr.Rec, rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      cron_step.pc.absurdF({Cr.has_job(i, ys) == True{} : Bool}, h)
    case r <> +rest:
      match r:
        case Cr.Raw{x}:
          pc.job_append(rest, ys, i, h)
        case Cr.Known{+j}:
          pc.or_mono(Nat.is_eq(Cr.Job.id(j), i), Cr.has_job(i, rest), Cr.has_job(i, List.append(&2, Cr.Rec, rest, ys)), h, q => pc.job_append(rest, ys, i, q))

def pc.has_append(xs: List<&2, Nat>, +ys: List<&2, Nat>, +t: Nat, h: {Cr.has(t, xs) == True{} : Bool}) -> {Cr.has(t, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      cron_step.pc.absurdF({Cr.has(t, ys) == True{} : Bool}, h)
    case +x <> +rest:
      pc.or_mono(Nat.is_eq(x, t), Cr.has(t, rest), Cr.has(t, List.append(&2, Nat, rest, ys)), h, q => pc.has_append(rest, ys, t, q))

def cron_step.pc.ND(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def pc.none_some_t(-t: Nat, h: {None{} == Some{t} : Maybe<&2, Nat>}) -> Empty:
  %h : cron_step.pc.ND(_)
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
      cron_step.pc.void({Cr.has(t, aside) == True{} : Bool}, pc.none_some_t(t, h))
    case Some{+x}:
      +xt = Equal.cong(Maybe<&2, Nat>, Nat, m => pc.MDP(m), Some{x}, Some{t}, h)
      %Equal.sym(Nat, x, t, xt) : {Bool.or(Nat.is_eq(_, t), Cr.has(t, aside)) == True{} : Bool}
      cron_step.pc.or_l(Nat.is_eq(t, t), Cr.has(t, aside), cron_step.pc.eq_refl(t))

def pc.heal_keep(bad: Maybe<&2, Nat>, +t: Nat, +aside: List<&2, Nat>, h: {Cr.has(t, aside) == True{} : Bool}) -> {Cr.has(t, Cr.heal(bad, aside)) == True{} : Bool}:
  match bad:
    case None{}:
      h
    case Some{+x}:
      cron_step.pc.or_r(Nat.is_eq(x, t), Cr.has(t, aside), h)

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
      (h => pc.raw_append(rs, [Cr.Raw{x}], t, h), (h => pc.job_append(rs, [Cr.Raw{x}], i, h), (h => h, (h => cron_step.pc.void(Or({None{} == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, aside) == True{} : Bool}), pc.none_some_t(t, h)), h => h))))
    case Some{+y}:
      pc.keeps_refl(t, i, Cr.S{Some{y}, rs, rd, dead, c, n, aside})

def pc.keeps_raw_claim(bad: Maybe<&2, Nat>, +x: Nat, +t: Nat, +i: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>) -> Cr.Keeps(t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [x]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      (h => h, (h => h, (h => pc.has_append(rd, [x], t, h), (h => cron_step.pc.void(Or({None{} == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, aside) == True{} : Bool}), pc.none_some_t(t, h)), h => h))))
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
          LABool.cron_step.pc.absurd(Cr.Keeps(t, i, Cr.S{bad, rs, rd, dead, c, n, aside}, Cr.S{Some{x}, Nil{}, Nil{}, dead, c, n, aside}), nc)

def pc.cron_never_drops(+s: Cr.S, +e: Cr.Ev, +t: Nat, +i: Nat) -> {Cr.Ev.is_corrupt(e) == False{} : Bool} -> Cr.Keeps(t, i, s, Cr.step(s, e)):
  nc => pc.never_drops(s, e, t, i, nc)

def Cron.cron_never_drops(s, e, t, i):
  pc.cron_never_drops(s, e, t, i)
