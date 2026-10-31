# eukhe: the proof of LAW cron_ids_distinct
# Every reachable file keeps an invariant: no two job records share an id,
# and every id is below the next fresh id. A step's `recs` keeps every id,
# a new job takes the fresh id (then the next one is fresh), a corrupt file
# holds none, a record this build cannot read has none.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/file.bend as LCfd
import ./base/logic.bend as LCfl

# The invariant
# -------------

def cfi.below(+n: Nat, rs: List<&2, Cr.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.and(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, t))
        case Cr.Raw{y}:
          cfi.below(n, t)

def cfi.ids(s: Cr.S) -> Nat:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      n

def cfi.ok(+s: Cr.S) -> Bool:
  Bool.and(CronFileView.distinct(Cr.S.recs(s)), cfi.below(cfi.ids(s), Cr.S.recs(s)))

# Nats
# ----

def cfi.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LCfl.cfl.absurdF({True{} == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cfi.lt_ne(p, q, h)

def cfi.lt_up(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LCfl.cfl.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      cfi.lt_up(p, q, h)

def cfi.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      cfi.lt_self(p)

# A step keeps every id
# ---------------------

def cfi.below_recs(+n: Nat, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> {cfi.below(n, Cr.recs(e, c, dead, rs)) == cfi.below(n, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Nat, CronFileView.id_of(Cr.job(e, c, dead, j)), CronFileView.id_of(j), LCfd.cfd.id_job(e, c, dead, j)) : {Bool.and(Nat.is_lt(_, n), cfi.below(n, Cr.recs(e, c, dead, t))) == Bool.and(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, t)) : Bool}
          %Equal.sym(Bool, cfi.below(n, Cr.recs(e, c, dead, t)), cfi.below(n, t), cfi.below_recs(n, e, c, dead, t)) : {Bool.and(Nat.is_lt(CronFileView.id_of(j), n), _) == Bool.and(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, t)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfi.below_recs(n, e, c, dead, t)

def cfi.ok_recs(+e: Cr.Ev, +b2: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +dead2: List<&2, Nat>, +c: Nat, +n: Nat, +a2: List<&2, Nat>, inv: {Bool.and(CronFileView.distinct(rs), cfi.below(n, rs)) == True{} : Bool}) -> {cfi.ok(Cr.S{b2, Cr.recs(e, c, dead, rs), rd, dead2, c, n, a2}) == True{} : Bool}:
  %Equal.sym(Bool, CronFileView.distinct(Cr.recs(e, c, dead, rs)), CronFileView.distinct(rs), LCfd.cfd.distinct_recs(e, c, dead, rs)) : {Bool.and(_, cfi.below(n, Cr.recs(e, c, dead, rs))) == True{} : Bool}
  %Equal.sym(Bool, cfi.below(n, Cr.recs(e, c, dead, rs)), cfi.below(n, rs), cfi.below_recs(n, e, c, dead, rs)) : {Bool.and(CronFileView.distinct(rs), _) == True{} : Bool}
  inv

def cfi.alive_recs(b: Bool, +e: Cr.Ev, +b1: Maybe<&2, Nat>, +a1: List<&2, Nat>, +bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +inv: {Bool.and(CronFileView.distinct(rs), cfi.below(n, rs)) == True{} : Bool}) -> {cfi.ok(Cr.step.alive(b, Cr.S{b1, Cr.recs(e, c, dead, rs), rd, dead, c, n, a1}, Cr.S{bad, rs, rd, dead, c, n, aside})) == True{} : Bool}:
  match b:
    case False{}:
      cfi.ok_recs(e, b1, rs, rd, dead, dead, c, n, a1, inv)
    case True{}:
      inv

# A new job takes the fresh id
# ----------------------------

def cfi.has_below(+n: Nat, rs: List<&2, Cr.Rec>, +h: {cfi.below(n, rs) == True{} : Bool}) -> {CronFileView.has_id(n, rs) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          +lt = LCfl.cfl.and_l(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, t), h)
          %Equal.sym(Bool, Nat.is_eq(CronFileView.id_of(j), n), False{}, cfi.lt_ne(CronFileView.id_of(j), n, lt)) : {Bool.or(_, CronFileView.has_id(n, t)) == False{} : Bool}
          cfi.has_below(n, t, LCfl.cfl.and_r(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, t), h))
        case Cr.Raw{y}:
          cfi.has_below(n, t, h)

def cfi.has_snoc(+x: Nat, t: List<&2, Cr.Rec>, +j: Cr.Job, +h1: {CronFileView.has_id(x, t) == False{} : Bool}, h2: {Nat.is_eq(CronFileView.id_of(j), x) == False{} : Bool}) -> {CronFileView.has_id(x, List.append(&2, Cr.Rec, t, [Cr.Known{j}])) == False{} : Bool}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(CronFileView.id_of(j), x), False{}, h2) : {Bool.or(_, False{}) == False{} : Bool}
      {==}
    case r <> +u:
      match r:
        case Cr.Known{+j2}:
          %Equal.sym(Bool, Nat.is_eq(CronFileView.id_of(j2), x), False{}, LCfd.cfd.has_head(j2, u, x, h1)) : {Bool.or(_, CronFileView.has_id(x, List.append(&2, Cr.Rec, u, [Cr.Known{j}]))) == False{} : Bool}
          cfi.has_snoc(x, u, j, LCfd.cfd.has_tail(j2, u, x, h1), h2)
        case Cr.Raw{y}:
          cfi.has_snoc(x, u, j, h1, h2)

def cfi.distinct_snoc(rs: List<&2, Cr.Rec>, +j: Cr.Job, +d: {CronFileView.distinct(rs) == True{} : Bool}, +h: {CronFileView.has_id(CronFileView.id_of(j), rs) == False{} : Bool}) -> {CronFileView.distinct(List.append(&2, Cr.Rec, rs, [Cr.Known{j}])) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j2}:
          +ne = LCfl.cfl.ne_comm(CronFileView.id_of(j2), CronFileView.id_of(j), LCfd.cfd.has_head(j2, t, CronFileView.id_of(j), h))
          %Equal.sym(Bool, CronFileView.has_id(CronFileView.id_of(j2), List.append(&2, Cr.Rec, t, [Cr.Known{j}])), False{}, cfi.has_snoc(CronFileView.id_of(j2), t, j, LCfd.cfd.distinct_head(j2, t, d), ne)) : {Bool.and(Bool.not(_), CronFileView.distinct(List.append(&2, Cr.Rec, t, [Cr.Known{j}]))) == True{} : Bool}
          cfi.distinct_snoc(t, j, LCfd.cfd.distinct_tail(j2, t, d), LCfd.cfd.has_tail(j2, t, CronFileView.id_of(j), h))
        case Cr.Raw{y}:
          cfi.distinct_snoc(t, j, d, h)

def cfi.below_up(+n: Nat, rs: List<&2, Cr.Rec>, +j: Cr.Job, +idn: {Nat.is_lt(CronFileView.id_of(j), 1n+n) == True{} : Bool}, +h: {cfi.below(n, rs) == True{} : Bool}) -> {cfi.below(1n+n, List.append(&2, Cr.Rec, rs, [Cr.Known{j}])) == True{} : Bool}:
  match rs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_lt(CronFileView.id_of(j), 1n+n), True{}, idn) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j2}:
          +lt = cfi.lt_up(CronFileView.id_of(j2), n, LCfl.cfl.and_l(Nat.is_lt(CronFileView.id_of(j2), n), cfi.below(n, t), h))
          %Equal.sym(Bool, Nat.is_lt(CronFileView.id_of(j2), 1n+n), True{}, lt) : {Bool.and(_, cfi.below(1n+n, List.append(&2, Cr.Rec, t, [Cr.Known{j}]))) == True{} : Bool}
          cfi.below_up(n, t, j, idn, LCfl.cfl.and_r(Nat.is_lt(CronFileView.id_of(j2), n), cfi.below(n, t), h))
        case Cr.Raw{y}:
          cfi.below_up(n, t, j, idn, h)

def cfi.create(b: Bool, +sc: Cr.Sched, +bad: Maybe<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +inv: {Bool.and(CronFileView.distinct(rs), cfi.below(n, rs)) == True{} : Bool}) -> {cfi.ok(Cr.step.alive(b, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})) == True{} : Bool}:
  match b:
    case False{}:
      +j = {Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}} : Cr.Job}
      +d = LCfl.cfl.and_l(CronFileView.distinct(rs), cfi.below(n, rs), inv)
      +bl = LCfl.cfl.and_r(CronFileView.distinct(rs), cfi.below(n, rs), inv)
      %Equal.sym(Bool, CronFileView.distinct(List.append(&2, Cr.Rec, rs, [Cr.Known{j}])), True{}, cfi.distinct_snoc(rs, j, d, cfi.has_below(n, rs, bl))) : {Bool.and(_, cfi.below(1n+n, List.append(&2, Cr.Rec, rs, [Cr.Known{j}]))) == True{} : Bool}
      cfi.below_up(n, rs, j, cfi.lt_self(n), bl)
    case True{}:
      inv

# A record this build cannot read has no id
# -----------------------------------------

def cfi.has_raw(+x: Nat, rs: List<&2, Cr.Rec>, +t: Nat) -> {CronFileView.has_id(x, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}])) == CronFileView.has_id(x, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +u:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Bool, CronFileView.has_id(x, List.append(&2, Cr.Rec, u, [Cr.Raw{t}])), CronFileView.has_id(x, u), cfi.has_raw(x, u, t)) : {Bool.or(Nat.is_eq(CronFileView.id_of(j), x), _) == Bool.or(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.has_id(x, u)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfi.has_raw(x, u, t)

def cfi.distinct_raw(rs: List<&2, Cr.Rec>, +t: Nat) -> {CronFileView.distinct(List.append(&2, Cr.Rec, rs, [Cr.Raw{t}])) == CronFileView.distinct(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +u:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Bool, CronFileView.has_id(CronFileView.id_of(j), List.append(&2, Cr.Rec, u, [Cr.Raw{t}])), CronFileView.has_id(CronFileView.id_of(j), u), cfi.has_raw(CronFileView.id_of(j), u, t)) : {Bool.and(Bool.not(_), CronFileView.distinct(List.append(&2, Cr.Rec, u, [Cr.Raw{t}]))) == Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), u)), CronFileView.distinct(u)) : Bool}
          %Equal.sym(Bool, CronFileView.distinct(List.append(&2, Cr.Rec, u, [Cr.Raw{t}])), CronFileView.distinct(u), cfi.distinct_raw(u, t)) : {Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), u)), _) == Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), u)), CronFileView.distinct(u)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfi.distinct_raw(u, t)

def cfi.below_raw(+n: Nat, rs: List<&2, Cr.Rec>, +t: Nat) -> {cfi.below(n, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}])) == cfi.below(n, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +u:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Bool, cfi.below(n, List.append(&2, Cr.Rec, u, [Cr.Raw{t}])), cfi.below(n, u), cfi.below_raw(n, u, t)) : {Bool.and(Nat.is_lt(CronFileView.id_of(j), n), _) == Bool.and(Nat.is_lt(CronFileView.id_of(j), n), cfi.below(n, u)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfi.below_raw(n, u, t)

def cfi.raw_job(bad: Maybe<&2, Nat>, +t: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +inv: {Bool.and(CronFileView.distinct(rs), cfi.below(n, rs)) == True{} : Bool}) -> {cfi.ok(Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})) == True{} : Bool}:
  match bad:
    case None{}:
      %Equal.sym(Bool, CronFileView.distinct(List.append(&2, Cr.Rec, rs, [Cr.Raw{t}])), CronFileView.distinct(rs), cfi.distinct_raw(rs, t)) : {Bool.and(_, cfi.below(n, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]))) == True{} : Bool}
      %Equal.sym(Bool, cfi.below(n, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}])), cfi.below(n, rs), cfi.below_raw(n, rs, t)) : {Bool.and(CronFileView.distinct(rs), _) == True{} : Bool}
      inv
    case Some{y}:
      inv

def cfi.raw_claim(bad: Maybe<&2, Nat>, +t: Nat, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +inv: {Bool.and(CronFileView.distinct(rs), cfi.below(n, rs)) == True{} : Bool}) -> {cfi.ok(Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})) == True{} : Bool}:
  match bad:
    case None{}:
      inv
    case Some{y}:
      inv

# Every step keeps the invariant
# ------------------------------

def cfi.step(s: Cr.S, +e: Cr.Ev, +inv: {cfi.ok(s) == True{} : Bool}) -> {cfi.ok(Cr.step(s, e)) == True{} : Bool}:
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          cfi.create(Cr.has(p, dead), sc, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Take{+p}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Take{p}, None{}, Cr.heal(bad, aside), bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Recover{+p}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Recover{p}, None{}, Cr.heal(bad, aside), bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Finish{+p, +i, +o}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Finish{p, i, o}, None{}, Cr.heal(bad, aside), bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Abort{+p}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Abort{p}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Cancel{+p, +i}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Cancel{p, i}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Resume{+p, +i}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Resume{p, i}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Pause{+p, +i}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Pause{p, i}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Stop{+p, +i}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Stop{p, i}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Delete{+p, +i}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Delete{p, i}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Edit{+p, +i, +k}:
          cfi.alive_recs(Cr.has(p, dead), Cr.Edit{p, i, k}, bad, aside, bad, rs, rd, dead, c, n, aside, inv)
        case Cr.Die{+p}:
          cfi.ok_recs(Cr.Die{p}, bad, rs, rd, dead, p <> dead, c, n, aside, inv)
        case Cr.Tick{+d}:
          inv
        case Cr.RawJob{+t}:
          cfi.raw_job(bad, t, rs, rd, dead, c, n, aside, inv)
        case Cr.RawClaim{+t}:
          cfi.raw_claim(bad, t, rs, rd, dead, c, n, aside, inv)
        case Cr.Corrupt{t}:
          {==}

def cfi.go(evs: List<&2, Cr.Ev>, +s: Cr.S, inv: {cfi.ok(s) == True{} : Bool}) -> {cfi.ok(Cr.go(evs, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      cfi.go(rest, Cr.step(s, e), cfi.step(s, e, inv))

def CronFileView.cron_ids_distinct(evs):
  +ok = cfi.go(evs, Cr.S.empty(), {==})
  LCfl.cfl.and_l(CronFileView.distinct(Cr.S.recs(Cr.run(evs))), cfi.below(cfi.ids(Cr.run(evs)), Cr.S.recs(Cr.run(evs))), ok)
