# eukhe: the proof of LAW cron_type_terms_exact
# Each predicate both ways: by induction on the records, by cases on a
# job, and, for the one-step predicates, part by part (the model's terms
# are the laws' by induction: ctt.has_raw, ctt.has_job, ctt.status,
# ct.has of cron_terms_exact).

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_terms.bend as CronTerms
import ../base/terms.bend as LT
import ./cron_terms_exact.bend as PCT

# Bools
# -----

def ctt.and_in(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      LT.lt.absurd({Bool.and(False{}, b) == True{} : Bool}, ha)

def ctt.imp_in(a: Bool, -b: Bool, f: {a == True{} : Bool} -> {b == True{} : Bool}) -> {CronTerms.imp_spec(a, b) == True{} : Bool}:
  match a:
    case True{}:
      f({==})
    case False{}:
      {==}

def ctt.imp_out(a: Bool, -b: Bool, h: {CronTerms.imp_spec(a, b) == True{} : Bool}, x: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LT.lt.absurd({b == True{} : Bool}, x)

# an implication between the model's Bools a2, b2 is the laws' implication
# between their specs a, b
def ctt.imp_in2(a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a2 == a : Bool}, eb: {b2 == b : Bool}, f: {a2 == True{} : Bool} -> {b2 == True{} : Bool}) -> {CronTerms.imp_spec(a, b) == True{} : Bool}:
  match a:
    case True{}:
      Equal.trans(Bool, b, b2, True{}, Equal.sym(Bool, b2, b, eb), f(ea))
    case False{}:
      {==}

def ctt.imp_out2(a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a2 == a : Bool}, eb: {b2 == b : Bool}, h: {CronTerms.imp_spec(a, b) == True{} : Bool}, x: {a2 == True{} : Bool}) -> {b2 == True{} : Bool}:
  match a:
    case True{}:
      Equal.trans(Bool, b2, b, True{}, eb, h)
    case False{}:
      LT.lt.absurd({b2 == True{} : Bool}, Equal.trans(Bool, False{}, a2, True{}, Equal.sym(Bool, a2, False{}, ea), x))

def ctt.eq_in(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), LT.lt.eq_refl(a))

def ctt.nil_in(-xs: List<&2, Nat>, e: {xs == Nil{} : List<&2, Nat>}) -> {CronTerms.is_nil_spec(xs) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, xs, Nil{}, e) : {CronTerms.is_nil_spec(_) == True{} : Bool}
  {==}

def ctt.nil_out(xs: List<&2, Nat>, h: {CronTerms.is_nil_spec(xs) == True{} : Bool}) -> {xs == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      LT.lt.absurd({(x <> t) == Nil{} : List<&2, Nat>}, h)

# Fires
# -----

def ctt.owns_in(cl: Maybe<&2, Cr.Claim>, +o: Nat, h: Cr.Owns(cl, o)) -> {CronTerms.owns_spec(cl, o) == True{} : Bool}:
  match cl:
    case None{}:
      match h:
    case Some{x}:
      match x:
        case Cr.Claim{occ, w}:
          ctt.eq_in(w, o, h)

def ctt.owns_out(cl: Maybe<&2, Cr.Claim>, +o: Nat, h: {CronTerms.owns_spec(cl, o) == True{} : Bool}) -> Cr.Owns(cl, o):
  match cl:
    case None{}:
      LT.lt.absurd(Cr.Owns(None{}, o), h)
    case Some{x}:
      match x:
        case Cr.Claim{occ, w}:
          LT.lt.eq_true(w, o, h)

def ctt.held_in(rs: List<&2, Nat>, +cl: Maybe<&2, Cr.Claim>, h: Cr.Held(rs, cl)) -> {CronTerms.held_spec(rs, cl) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case o <> t:
      match t:
        case Nil{}:
          ctt.owns_in(cl, o, h)
        case x <> u:
          match h:

def ctt.held_out(rs: List<&2, Nat>, +cl: Maybe<&2, Cr.Claim>, h: {CronTerms.held_spec(rs, cl) == True{} : Bool}) -> Cr.Held(rs, cl):
  match rs:
    case Nil{}:
      Unit{}
    case o <> t:
      match t:
        case Nil{}:
          ctt.owns_out(cl, o, h)
        case x <> u:
          LT.lt.absurd(Cr.Held(o <> (x <> u), cl), h)

def ctt.desc_from_in(t: List<&2, Nat>, +x: Nat, d: Cr.DescFrom(x, t)) -> {CronTerms.desc_from_spec(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +y <> +u:
      (lt, rest) = d
      ctt.and_in(Nat.is_lt(y, x), CronTerms.desc_from_spec(u, y), lt, ctt.desc_from_in(u, y, rest))

def ctt.desc_from_out(t: List<&2, Nat>, +x: Nat, +c: {CronTerms.desc_from_spec(t, x) == True{} : Bool}) -> Cr.DescFrom(x, t):
  match t:
    case Nil{}:
      Unit{}
    case +y <> +u:
      (LT.lt.and_l(Nat.is_lt(y, x), CronTerms.desc_from_spec(u, y), c), ctt.desc_from_out(u, y, LT.lt.and_r(Nat.is_lt(y, x), CronTerms.desc_from_spec(u, y), c)))

def ctt.desc_in(ss: List<&2, Nat>, d: Cr.Desc(ss)) -> {CronTerms.desc_spec(ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +x <> t:
      ctt.desc_from_in(t, x, d)

def ctt.desc_out(ss: List<&2, Nat>, c: {CronTerms.desc_spec(ss) == True{} : Bool}) -> Cr.Desc(ss):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> t:
      ctt.desc_from_out(t, x, c)

def ctt.once_in(s: Cr.Sched, ss: List<&2, Nat>, o: Cr.OnceOnce(s, ss)) -> {CronTerms.once_once_spec(s, ss) == True{} : Bool}:
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          {==}
        case x <> t:
          ctt.nil_in(t, o)
    case Cr.Every{k}:
      {==}

def ctt.once_out(s: Cr.Sched, ss: List<&2, Nat>, c: {CronTerms.once_once_spec(s, ss) == True{} : Bool}) -> Cr.OnceOnce(s, ss):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case x <> t:
          ctt.nil_out(t, c)
    case Cr.Every{k}:
      Unit{}

def ctt.fires_in(j: Cr.Job, f: Cr.Fires(j)) -> {CronTerms.fires_spec(j) == True{} : Bool}:
  match j:
    case Cr.Job{i, +s, st, nx, k, +cl, +rs, +ss, h}:
      (a, bc) = f
      (b, c) = bc
      ctt.and_in(CronTerms.held_spec(rs, cl), Bool.and(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss)), ctt.held_in(rs, cl, a), ctt.and_in(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss), ctt.desc_in(ss, b), ctt.once_in(s, ss, c)))

def ctt.fires_out(j: Cr.Job, +c: {CronTerms.fires_spec(j) == True{} : Bool}) -> Cr.Fires(j):
  match j:
    case Cr.Job{i, +s, st, nx, k, +cl, +rs, +ss, h}:
      +r = LT.lt.and_r(CronTerms.held_spec(rs, cl), Bool.and(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss)), c)
      (ctt.held_out(rs, cl, LT.lt.and_l(CronTerms.held_spec(rs, cl), Bool.and(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss)), c)), (ctt.desc_out(ss, LT.lt.and_l(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss), r)), ctt.once_out(s, ss, LT.lt.and_r(CronTerms.desc_spec(ss), CronTerms.once_once_spec(s, ss), r))))

def ctt.fires_all_in(rs: List<&2, Cr.Rec>, h: Cr.FiresAll(rs)) -> {CronTerms.fires_all_spec(rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (a, b) = h
          ctt.and_in(CronTerms.fires_spec(j), CronTerms.fires_all_spec(t), ctt.fires_in(j, a), ctt.fires_all_in(t, b))
        case Cr.Raw{x}:
          ctt.fires_all_in(t, h)

def ctt.fires_all_out(rs: List<&2, Cr.Rec>, +c: {CronTerms.fires_all_spec(rs) == True{} : Bool}) -> Cr.FiresAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (ctt.fires_out(j, LT.lt.and_l(CronTerms.fires_spec(j), CronTerms.fires_all_spec(t), c)), ctt.fires_all_out(t, LT.lt.and_r(CronTerms.fires_spec(j), CronTerms.fires_all_spec(t), c)))
        case Cr.Raw{x}:
          ctt.fires_all_out(t, c)

# Ends
# ----

def ctt.ends_in(j: Cr.Job, e: Cr.Ends(j)) -> {CronTerms.ends_spec(j) == True{} : Bool}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              ctt.nil_in(rs, e)
            case Cr.Cancelled{}:
              {==}
        case Cr.Every{n}:
          {==}

def ctt.ends_out(j: Cr.Job, c: {CronTerms.ends_spec(j) == True{} : Bool}) -> Cr.Ends(j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              Unit{}
            case Cr.Paused{}:
              Unit{}
            case Cr.Finished{}:
              ctt.nil_out(rs, c)
            case Cr.Cancelled{}:
              Unit{}
        case Cr.Every{n}:
          Unit{}

def ctt.ends_all_in(rs: List<&2, Cr.Rec>, h: Cr.EndsAll(rs)) -> {CronTerms.ends_all_spec(rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (a, b) = h
          ctt.and_in(CronTerms.ends_spec(j), CronTerms.ends_all_spec(t), ctt.ends_in(j, a), ctt.ends_all_in(t, b))
        case Cr.Raw{x}:
          ctt.ends_all_in(t, h)

def ctt.ends_all_out(rs: List<&2, Cr.Rec>, +c: {CronTerms.ends_all_spec(rs) == True{} : Bool}) -> Cr.EndsAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (ctt.ends_out(j, LT.lt.and_l(CronTerms.ends_spec(j), CronTerms.ends_all_spec(t), c)), ctt.ends_all_out(t, LT.lt.and_r(CronTerms.ends_spec(j), CronTerms.ends_all_spec(t), c)))
        case Cr.Raw{x}:
          ctt.ends_all_out(t, c)

# Stops
# -----

def ctt.trail(h: List<&2, Cr.Mark>) -> {Cr.trail(h) == CronTerms.trail_spec(h) : Nat}:
  match h:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Cr.MWin{}:
          {==}
        case Cr.MLoss{}:
          %ctt.trail(t) : {1n+Cr.trail(t) == 1n+_ : Nat}
          {==}
        case Cr.MReset{}:
          {==}

def ctt.act_in(st: Cr.Status, +n: Nat, a: Cr.Act(st, n)) -> {CronTerms.act_spec(st, n) == True{} : Bool}:
  match st:
    case Cr.Active{}:
      a
    case Cr.Paused{}:
      {==}
    case Cr.Finished{}:
      {==}
    case Cr.Cancelled{}:
      {==}

def ctt.act_out(st: Cr.Status, +n: Nat, c: {CronTerms.act_spec(st, n) == True{} : Bool}) -> Cr.Act(st, n):
  match st:
    case Cr.Active{}:
      c
    case Cr.Paused{}:
      Unit{}
    case Cr.Finished{}:
      Unit{}
    case Cr.Cancelled{}:
      Unit{}

def ctt.stops_in(j: Cr.Job, p: Cr.Stops(j)) -> {CronTerms.stops_spec(j) == True{} : Bool}:
  match j:
    case Cr.Job{i, s, +st, nx, k, cl, rs, ss, +h}:
      (a, b) = p
      %ctt.trail(h) : {Bool.and(Nat.is_le(_, CronTerms.cap_spec()), CronTerms.act_spec(st, _)) == True{} : Bool}
      ctt.and_in(Nat.is_le(Cr.trail(h), CronTerms.cap_spec()), CronTerms.act_spec(st, Cr.trail(h)), a, ctt.act_in(st, Cr.trail(h), b))

def ctt.stops_out(j: Cr.Job, +c: {CronTerms.stops_spec(j) == True{} : Bool}) -> Cr.Stops(j):
  match j:
    case Cr.Job{i, s, +st, nx, k, cl, rs, ss, +h}:
      %Equal.sym(Nat, Cr.trail(h), CronTerms.trail_spec(h), ctt.trail(h)) : ({Nat.is_le(_, Cr.CAP()) == True{} : Bool} & Cr.Act(st, _))
      (LT.lt.and_l(Nat.is_le(CronTerms.trail_spec(h), CronTerms.cap_spec()), CronTerms.act_spec(st, CronTerms.trail_spec(h)), c), ctt.act_out(st, CronTerms.trail_spec(h), LT.lt.and_r(Nat.is_le(CronTerms.trail_spec(h), CronTerms.cap_spec()), CronTerms.act_spec(st, CronTerms.trail_spec(h)), c)))

def ctt.stops_all_in(rs: List<&2, Cr.Rec>, h: Cr.StopsAll(rs)) -> {CronTerms.stops_all_spec(rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (a, b) = h
          ctt.and_in(CronTerms.stops_spec(j), CronTerms.stops_all_spec(t), ctt.stops_in(j, a), ctt.stops_all_in(t, b))
        case Cr.Raw{x}:
          ctt.stops_all_in(t, h)

def ctt.stops_all_out(rs: List<&2, Cr.Rec>, +c: {CronTerms.stops_all_spec(rs) == True{} : Bool}) -> Cr.StopsAll(rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          (ctt.stops_out(j, LT.lt.and_l(CronTerms.stops_spec(j), CronTerms.stops_all_spec(t), c)), ctt.stops_all_out(t, LT.lt.and_r(CronTerms.stops_spec(j), CronTerms.stops_all_spec(t), c)))
        case Cr.Raw{x}:
          ctt.stops_all_out(t, c)

# Keeps
# -----

def ctt.has_raw(+t: Nat, rs: List<&2, Cr.Rec>) -> {Cr.has_raw(t, rs) == CronTerms.has_raw_spec(t, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Cr.Raw{+x}:
          %ctt.has_raw(t, rest) : {Bool.or(Nat.is_eq(x, t), Cr.has_raw(t, rest)) == Bool.or(Nat.is_eq(x, t), _) : Bool}
          {==}
        case Cr.Known{j}:
          ctt.has_raw(t, rest)

def ctt.has_job(+i: Nat, rs: List<&2, Cr.Rec>) -> {Cr.has_job(i, rs) == CronTerms.has_job_spec(i, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Cr.Raw{x}:
          ctt.has_job(i, rest)
        case Cr.Known{j}:
          match j:
            case Cr.Job{+id, s, st, nx, k, cl, ru, ss, h}:
              %ctt.has_job(i, rest) : {Bool.or(Nat.is_eq(id, i), Cr.has_job(i, rest)) == Bool.or(Nat.is_eq(id, i), _) : Bool}
              {==}

def ctt.has(+t: Nat, xs: List<&2, Nat>) -> {Cr.has(t, xs) == CronTerms.has_spec(t, xs) : Bool}:
  Equal.sym(Bool, CronTerms.has_spec(t, xs), Cr.has(t, xs), PCT.ct.has(t, xs))

def ctt.bad_out(m: Maybe<&2, Nat>, +t: Nat, h: {CronTerms.is_bad_spec(m, t) == True{} : Bool}) -> {m == Some{t} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      LT.lt.absurd({None{} == Some{t} : Maybe<&2, Nat>}, h)
    case Some{+x}:
      %LT.lt.eq_true(x, t, h) : {Some{x} == Some{_} : Maybe<&2, Nat>}
      {==}

def ctt.bad_in(-m: Maybe<&2, Nat>, +t: Nat, e: {m == Some{t} : Maybe<&2, Nat>}) -> {CronTerms.is_bad_spec(m, t) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, m, Some{t}, e) : {CronTerms.is_bad_spec(_, t) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(t, t), LT.lt.eq_refl(t))

def ctt.aside_in(+b2: Maybe<&2, Nat>, +t: Nat, +a2: List<&2, Nat>, o: Or({b2 == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, a2) == True{} : Bool})) -> {Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2)) == True{} : Bool}:
  match o:
    case Inl{e}:
      LT.lt.or_l(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2), ctt.bad_in(b2, t, e))
    case Inr{x}:
      LT.lt.or_r(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2), Equal.trans(Bool, CronTerms.has_spec(t, a2), Cr.has(t, a2), True{}, PCT.ct.has(t, a2), x))

def ctt.aside_out(+b2: Maybe<&2, Nat>, +t: Nat, +a2: List<&2, Nat>, h: {Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2)) == True{} : Bool}) -> Or({b2 == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, a2) == True{} : Bool}):
  LT.lt.or_elim({CronTerms.is_bad_spec(b2, t) == True{} : Bool}, {CronTerms.has_spec(t, a2) == True{} : Bool}, Or({b2 == Some{t} : Maybe<&2, Nat>}, {Cr.has(t, a2) == True{} : Bool}), LT.lt.or_cases(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2), h), e => Inl{ctt.bad_out(b2, t, e)}, x => Inr{Equal.trans(Bool, Cr.has(t, a2), CronTerms.has_spec(t, a2), True{}, ctt.has(t, a2), x)})

def ctt.keeps_in(+t: Nat, +i: Nat, s: Cr.S, s2: Cr.S, kp: Cr.Keeps(t, i, s, s2)) -> {CronTerms.keeps_spec(t, i, s, s2) == True{} : Bool}:
  match s:
    case Cr.S{+b, +rs, +rd, dead, c, n, +a}:
      match s2:
        case Cr.S{+b2, +rs2, +rd2, dead2, c2, n2, +a2}:
          (k1, k25) = kp
          (k2, k35) = k25
          (k3, k45) = k35
          (k4, k5) = k45
          ctt.and_in(CronTerms.imp_spec(CronTerms.has_raw_spec(t, rs), CronTerms.has_raw_spec(t, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))))), ctt.imp_in2(CronTerms.has_raw_spec(t, rs), Cr.has_raw(t, rs), CronTerms.has_raw_spec(t, rs2), Cr.has_raw(t, rs2), ctt.has_raw(t, rs), ctt.has_raw(t, rs2), k1), ctt.and_in(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)))), ctt.imp_in2(CronTerms.has_job_spec(i, rs), Cr.has_job(i, rs), CronTerms.has_job_spec(i, rs2), Cr.has_job(i, rs2), ctt.has_job(i, rs), ctt.has_job(i, rs2), k2), ctt.and_in(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))), ctt.imp_in2(CronTerms.has_spec(t, rd), Cr.has(t, rd), CronTerms.has_spec(t, rd2), Cr.has(t, rd2), ctt.has(t, rd), ctt.has(t, rd2), k3), ctt.and_in(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)), ctt.imp_in(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2)), x => ctt.aside_in(b2, t, a2, k4(ctt.bad_out(b, t, x)))), ctt.imp_in2(CronTerms.has_spec(t, a), Cr.has(t, a), CronTerms.has_spec(t, a2), Cr.has(t, a2), ctt.has(t, a), ctt.has(t, a2), k5)))))

def ctt.keeps_out(+t: Nat, +i: Nat, s: Cr.S, s2: Cr.S, +h: {CronTerms.keeps_spec(t, i, s, s2) == True{} : Bool}) -> Cr.Keeps(t, i, s, s2):
  match s:
    case Cr.S{+b, +rs, +rd, dead, c, n, +a}:
      match s2:
        case Cr.S{+b2, +rs2, +rd2, dead2, c2, n2, +a2}:
          +h1 = LT.lt.and_l(CronTerms.imp_spec(CronTerms.has_raw_spec(t, rs), CronTerms.has_raw_spec(t, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))))), h)
          +r1 = LT.lt.and_r(CronTerms.imp_spec(CronTerms.has_raw_spec(t, rs), CronTerms.has_raw_spec(t, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))))), h)
          +h2 = LT.lt.and_l(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)))), r1)
          +r2 = LT.lt.and_r(CronTerms.imp_spec(CronTerms.has_job_spec(i, rs), CronTerms.has_job_spec(i, rs2)), Bool.and(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)))), r1)
          +h3 = LT.lt.and_l(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))), r2)
          +r3 = LT.lt.and_r(CronTerms.imp_spec(CronTerms.has_spec(t, rd), CronTerms.has_spec(t, rd2)), Bool.and(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2))), r2)
          +h4 = LT.lt.and_l(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)), r3)
          +h5 = LT.lt.and_r(CronTerms.imp_spec(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2))), CronTerms.imp_spec(CronTerms.has_spec(t, a), CronTerms.has_spec(t, a2)), r3)
          (x => ctt.imp_out2(CronTerms.has_raw_spec(t, rs), Cr.has_raw(t, rs), CronTerms.has_raw_spec(t, rs2), Cr.has_raw(t, rs2), ctt.has_raw(t, rs), ctt.has_raw(t, rs2), h1, x), (x => ctt.imp_out2(CronTerms.has_job_spec(i, rs), Cr.has_job(i, rs), CronTerms.has_job_spec(i, rs2), Cr.has_job(i, rs2), ctt.has_job(i, rs), ctt.has_job(i, rs2), h2, x), (x => ctt.imp_out2(CronTerms.has_spec(t, rd), Cr.has(t, rd), CronTerms.has_spec(t, rd2), Cr.has(t, rd2), ctt.has(t, rd), ctt.has(t, rd2), h3, x), (x => ctt.aside_out(b2, t, a2, ctt.imp_out(CronTerms.is_bad_spec(b, t), Bool.or(CronTerms.is_bad_spec(b2, t), CronTerms.has_spec(t, a2)), h4, ctt.bad_in(b, t, x))), x => ctt.imp_out2(CronTerms.has_spec(t, a), Cr.has(t, a), CronTerms.has_spec(t, a2), Cr.has(t, a2), ctt.has(t, a), ctt.has(t, a2), h5, x)))))

# StaysPaused
# -----------

def ctt.pick(b: Bool, st: Cr.Status, rest: Maybe<&2, Cr.Status>) -> {Cr.status_of.pick(b, st, rest) == CronTerms.status_spec.pick(b, st, rest) : Maybe<&2, Cr.Status>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ctt.status(+i: Nat, rs: List<&2, Cr.Rec>) -> {Cr.status_of(i, rs) == CronTerms.status_spec(i, rs) : Maybe<&2, Cr.Status>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Raw{x}:
          ctt.status(i, t)
        case Cr.Known{j}:
          match j:
            case Cr.Job{+id, s, +st, nx, k, cl, ru, ss, h}:
              %ctt.status(i, t) : {Cr.status_of.pick(Nat.is_eq(id, i), st, Cr.status_of(i, t)) == CronTerms.status_spec.pick(Nat.is_eq(id, i), st, _) : Maybe<&2, Cr.Status>}
              ctt.pick(Nat.is_eq(id, i), st, Cr.status_of(i, t))

def ctt.paused_out(m: Maybe<&2, Cr.Status>, h: {CronTerms.paused_spec(m) == True{} : Bool}) -> {m == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}:
  match m:
    case None{}:
      LT.lt.absurd({None{} == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, h)
    case Some{st}:
      match st:
        case Cr.Active{}:
          LT.lt.absurd({Some{Cr.Active{}} == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          LT.lt.absurd({Some{Cr.Finished{}} == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, h)
        case Cr.Cancelled{}:
          LT.lt.absurd({Some{Cr.Cancelled{}} == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, h)

def ctt.paused_in(-m: Maybe<&2, Cr.Status>, e: {m == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}) -> {CronTerms.paused_spec(m) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Cr.Status>, m, Some{Cr.Paused{}}, e) : {CronTerms.paused_spec(_) == True{} : Bool}
  {==}

def ctt.gone_out(m: Maybe<&2, Cr.Status>, h: {CronTerms.gone_spec(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Cr.Status>}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      LT.lt.absurd({Some{st} == None{} : Maybe<&2, Cr.Status>}, h)

def ctt.gone_in(-m: Maybe<&2, Cr.Status>, e: {m == None{} : Maybe<&2, Cr.Status>}) -> {CronTerms.gone_spec(m) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Cr.Status>, m, None{}, e) : {CronTerms.gone_spec(_) == True{} : Bool}
  {==}

def ctt.stay_in(+m: Maybe<&2, Cr.Status>, o: Or({m == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, {m == None{} : Maybe<&2, Cr.Status>})) -> {Bool.or(CronTerms.paused_spec(m), CronTerms.gone_spec(m)) == True{} : Bool}:
  match o:
    case Inl{e}:
      LT.lt.or_l(CronTerms.paused_spec(m), CronTerms.gone_spec(m), ctt.paused_in(m, e))
    case Inr{e}:
      LT.lt.or_r(CronTerms.paused_spec(m), CronTerms.gone_spec(m), ctt.gone_in(m, e))

def ctt.stay_out(+m: Maybe<&2, Cr.Status>, h: {Bool.or(CronTerms.paused_spec(m), CronTerms.gone_spec(m)) == True{} : Bool}) -> Or({m == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, {m == None{} : Maybe<&2, Cr.Status>}):
  LT.lt.or_elim({CronTerms.paused_spec(m) == True{} : Bool}, {CronTerms.gone_spec(m) == True{} : Bool}, Or({m == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, {m == None{} : Maybe<&2, Cr.Status>}), LT.lt.or_cases(CronTerms.paused_spec(m), CronTerms.gone_spec(m), h), e => Inl{ctt.paused_out(m, e)}, e => Inr{ctt.gone_out(m, e)})

def ctt.paused_keep_in(+i: Nat, s: Cr.S, s2: Cr.S, k: Cr.StaysPaused(i, s, s2)) -> {CronTerms.stays_paused_spec(i, s, s2) == True{} : Bool}:
  match s:
    case Cr.S{b, +rs, rd, dead, c, n, a}:
      match s2:
        case Cr.S{b2, +rs2, rd2, dead2, c2, n2, a2}:
          %ctt.status(i, rs) : {CronTerms.imp_spec(CronTerms.paused_spec(_), Bool.or(CronTerms.paused_spec(CronTerms.status_spec(i, rs2)), CronTerms.gone_spec(CronTerms.status_spec(i, rs2)))) == True{} : Bool}
          %ctt.status(i, rs2) : {CronTerms.imp_spec(CronTerms.paused_spec(Cr.status_of(i, rs)), Bool.or(CronTerms.paused_spec(_), CronTerms.gone_spec(_))) == True{} : Bool}
          ctt.imp_in(CronTerms.paused_spec(Cr.status_of(i, rs)), Bool.or(CronTerms.paused_spec(Cr.status_of(i, rs2)), CronTerms.gone_spec(Cr.status_of(i, rs2))), x => ctt.stay_in(Cr.status_of(i, rs2), k(ctt.paused_out(Cr.status_of(i, rs), x))))

def ctt.paused_keep_out(+i: Nat, s: Cr.S, s2: Cr.S, h: {CronTerms.stays_paused_spec(i, s, s2) == True{} : Bool}) -> Cr.StaysPaused(i, s, s2):
  match s:
    case Cr.S{b, +rs, rd, dead, c, n, a}:
      match s2:
        case Cr.S{b2, +rs2, rd2, dead2, c2, n2, a2}:
          %Equal.sym(Maybe<&2, Cr.Status>, Cr.status_of(i, rs), CronTerms.status_spec(i, rs), ctt.status(i, rs)) : ({_ == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>} -> Or({Cr.status_of(i, rs2) == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, {Cr.status_of(i, rs2) == None{} : Maybe<&2, Cr.Status>}))
          %Equal.sym(Maybe<&2, Cr.Status>, Cr.status_of(i, rs2), CronTerms.status_spec(i, rs2), ctt.status(i, rs2)) : ({CronTerms.status_spec(i, rs) == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>} -> Or({_ == Some{Cr.Paused{}} : Maybe<&2, Cr.Status>}, {_ == None{} : Maybe<&2, Cr.Status>}))
          x => ctt.stay_out(CronTerms.status_spec(i, rs2), ctt.imp_out(CronTerms.paused_spec(CronTerms.status_spec(i, rs)), Bool.or(CronTerms.paused_spec(CronTerms.status_spec(i, rs2)), CronTerms.gone_spec(CronTerms.status_spec(i, rs2))), h, ctt.paused_in(CronTerms.status_spec(i, rs), x)))

# CronTerms

def CronTerms.cron_type_terms_exact(rs, t, i, s, s2):
  ((f => ctt.fires_all_in(rs, f), c => ctt.fires_all_out(rs, c)), ((e => ctt.ends_all_in(rs, e), c => ctt.ends_all_out(rs, c)), ((p => ctt.stops_all_in(rs, p), c => ctt.stops_all_out(rs, c)), ((k => ctt.keeps_in(t, i, s, s2, k), c => ctt.keeps_out(t, i, s, s2, c)), (k => ctt.paused_keep_in(i, s, s2, k), c => ctt.paused_keep_out(i, s, s2, c))))))
