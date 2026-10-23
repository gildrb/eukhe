# eukhe: lemmas the proofs of area cron share: cron

import Base
import ../../../bend/cron.bend as Cr
import ./bool.bend as LABool
import ./list.bend as LAList
import ./logic.bend as LALogic
import ./nat.bend as LANat

# A claim keeps the invariant
# ---------------------------

# a next run rolled from c lies after every occurrence at or before c
def pc.below_adv(+s: Cr.Sched, +c: Nat, +x: Nat, +h: {Nat.is_le(x, c) == True{} : Bool}) -> LALogic.pc.Below(x, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      LANat.pc.lt_add(x, c, q, h)

def pc.top_pair(+s: Cr.Sched, +c: Nat, +x: Nat, +a: {Nat.is_le(x, c) == True{} : Bool}) -> ({Nat.is_le(x, c) == True{} : Bool} & LALogic.pc.Below(x, Cr.adv(s, c))):
  (a, pc.below_adv(s, c, x, a))

def pc.top_adv(+ss: List<&2, Nat>, +s: Cr.Sched, +c: Nat, -nx: Maybe<&2, Nat>, t: LALogic.pc.Top(ss, c, nx)) -> LALogic.pc.Top(ss, c, Cr.adv(s, c)):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      pc.top_pair(s, c, x, a)

def pc.once_adv(+s: Cr.Sched, +ss: List<&2, Nat>, +c: Nat, -nx: Maybe<&2, Nat>, o: LALogic.pc.OnceG(s, ss, nx)) -> LALogic.pc.OnceG(s, ss, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case +x <> +t:
          (a, b) = o
          (a, {==})
    case Cr.Every{q}:
      Unit{}

def pc.ends_active(+s: Cr.Sched, -rs: List<&2, Nat>) -> Cr.EndsOf(s, Cr.Active{}, rs):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}

# the new occurrence n lies after every one that started
def pc.desc_push(+ss: List<&2, Nat>, +n: Nat, -c: Nat, d: Cr.Desc(ss), t: LALogic.pc.Top(ss, c, Some{n})) -> Cr.DescFrom(n, ss):
  match ss:
    case Nil{}:
      Unit{}
    case +y <> +u:
      (a, b) = t
      (b, d)

def pc.once_new(+s: Cr.Sched, +ss: List<&2, Nat>, +n: Nat, +c: Nat, o: LALogic.pc.OnceG(s, ss, Some{n})) -> LALogic.pc.OnceG(s, n <> ss, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          ({==}, {==})
        case +x <> +t:
          (a, b) = o
          LALogic.pc.some_none(({x <> t == Nil{} : List<&2, Nat>} & {None{} == None{} : Maybe<&2, Nat>}), n, b)
    case Cr.Every{q}:
      Unit{}

# a due job with no claim: the claim, the run and the start are p's
def pc.take_new(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +le: {Nat.is_le(n, c) == True{} : Bool}, +al: {Cr.has(p, dead) == False{} : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, None{}, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Cr.adv(s, c), k, Some{Cr.Claim{n, p}}, p <> rs, n <> ss, h}):
  match rs:
    case Nil{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      ({==}, ((al, Unit{}), (pc.desc_push(ss, n, c, h3, h4), (pc.top_pair(s, c, n, le), (pc.once_new(s, ss, n, c, h5), (h6, pc.ends_active(s, [p])))))))
    case +o <> +t:
      match t:
        case Nil{}:
          (h1, g2) = g
          match h1:
        case +x <> +u:
          (h1, g2) = g
          match h1:

# a due job with a claim only rolls its next run
def pc.take_skip(+c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, g: LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, Some{x}, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Cr.adv(s, c), k, Some{x}, rs, ss, h}):
  (h1, g2) = g
  (h2, g3) = g2
  (h3, g4) = g3
  (h4, g5) = g4
  (h5, g6) = g5
  (h6, h7) = g6
  (h1, (h2, (h3, (pc.top_adv(ss, s, c, Some{n}, h4), (pc.once_adv(s, ss, c, Some{n}, h5), (h6, h7))))))

def pc.take_due(b: Bool, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +eq: {Nat.is_le(n, c) == b : Bool}, +al: {Cr.has(p, dead) == False{} : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match cl:
        case None{}:
          pc.take_new(p, c, dead, i, s, n, k, rs, ss, h, eq, al, g)
        case Some{+x}:
          pc.take_skip(c, dead, i, s, n, k, x, rs, ss, h, g)

def pc.take_nx(+nx: Maybe<&2, Nat>, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +al: {Cr.has(p, dead) == False{} : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, nx, k, cl, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.take.next(p, c, i, s, nx, k, cl, rs, ss, h)):
  match nx:
    case None{}:
      g
    case Some{+n}:
      pc.take_due(Nat.is_le(n, c), p, c, dead, i, s, n, k, cl, rs, ss, h, {==}, al, g)

def pc.g_take(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +al: {Cr.has(p, dead) == False{} : Bool}, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.take(p, c, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          pc.take_nx(nx, p, c, dead, i, s, k, cl, rs, ss, h, al, g)
        case Cr.Paused{}:
          g
        case Cr.Finished{}:
          g
        case Cr.Cancelled{}:
          g

def pc.ends_nil(+s: Cr.Sched, +st: Cr.Status) -> Cr.EndsOf(s, st, Nil{}):
  match s:
    case Cr.Once{d}:
      match st:
        case Cr.Finished{}:
          {==}
        case Cr.Active{}:
          Unit{}
        case Cr.Paused{}:
          Unit{}
        case Cr.Cancelled{}:
          Unit{}
    case Cr.Every{q}:
      Unit{}

def pc.ends_cancel(+s: Cr.Sched, -rs: List<&2, Nat>) -> Cr.EndsOf(s, Cr.Cancelled{}, rs):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}

def pc.clears_at(+p: Nat, +o: Nat, +w: Nat, +dead: List<&2, Nat>, ow: {o == w : Nat}, nc: {Cr.clears(p, w, [w], dead) == False{} : Bool}) -> {Cr.clears(p, o, [w], dead) == False{} : Bool}:
  %Equal.sym(Nat, o, w, ow) : {Cr.clears(p, _, [w], dead) == False{} : Bool}
  nc

# a claim a recovery clears has no run: the run of an alive process
# holds it, and only its owner runs it
def pc.rec_none(+p: Nat, +o: Nat, +w: Nat, +dead: List<&2, Nat>, ow: {o == w : Nat}, live: {Cr.has(w, dead) == False{} : Bool}, eq: {Cr.clears(p, o, [w], dead) == True{} : Bool}) -> Empty:
  +no = pc.clears_at(p, o, w, dead, ow, LABool.pc.no_clear(Nat.is_eq(w, p), Cr.has(w, dead), live))
  LALogic.cron.pc.absurd(Empty, Equal.trans(Bool, True{}, Cr.clears(p, o, [w], dead), False{}, Equal.sym(Bool, Cr.clears(p, o, [w], dead), True{}, eq), no))

def pc.rec_end(+s: Cr.Sched, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Cr.Claim, g: LALogic.pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, nx, k, Some{x}, Nil{}, ss, h})) -> LALogic.pc.G(c, dead, Cr.recover.end(Cr.is_once(s), i, s, nx, k, Nil{}, ss, h)):
  match s:
    case Cr.Once{+d}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (LALogic.pc.once_none(Cr.Once{d}, ss, nx, h5), (LANat.pc.cnt_down(Cr.Finished{}, k, h, h6), {==}))))))
    case Cr.Every{q}:
      g

def pc.rec_go(b: Bool, +rs: List<&2, Nat>, +st: Cr.Status, +p: Nat, +o: Nat, +xo: Nat, +dead: List<&2, Nat>, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eq: {Cr.clears(p, o, rs, dead) == b : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{xo, o}}, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.recover.go(b, i, s, st, nx, k, Cr.Claim{xo, o}, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match rs:
        case Nil{}:
          match st:
            case Cr.Active{}:
              pc.rec_end(s, c, dead, i, nx, k, ss, h, Cr.Claim{xo, o}, g)
            case Cr.Paused{}:
              g
            case Cr.Finished{}:
              g
            case Cr.Cancelled{}:
              g
        case +w <> +t:
          match t:
            case Nil{}:
              (h1, g2) = g
              (h2, g3) = g2
              (live, u) = h2
              LALogic.cron.pc.void(LALogic.pc.G(c, dead, Cr.recover.go(True{}, i, s, st, nx, k, Cr.Claim{xo, o}, [w], ss, h)), pc.rec_none(p, o, w, dead, h1, live, eq))
            case +y <> +v:
              (h1, g2) = g
              match h1:

def pc.g_recover(+p: Nat, +dead: List<&2, Nat>, +c: Nat, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.recover(p, dead, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          g
        case Some{+x}:
          match x:
            case Cr.Claim{+xo, +o}:
              pc.rec_go(Cr.clears(p, o, rs, dead), rs, st, p, o, xo, dead, c, i, s, nx, k, ss, h, {==}, g)

def pc.top_fail(+ss: List<&2, Nat>, +c: Nat, +nx: Maybe<&2, Nat>, +k: Nat, t: LALogic.pc.Top(ss, c, nx)) -> LALogic.pc.Top(ss, c, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))}):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      LANat.pc.top_fail2(x, c, nx, k, a, b)

def pc.fin_fail(b: Bool, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +q: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +eqb: {Nat.is_lt(1n+k, Cr.CAP()) == b : Bool}, h3: Cr.Desc(ss), h4: LALogic.pc.Top(ss, c, nx), +ek: {k == Cr.trail(h) : Nat}, +lt: {Nat.is_lt(k, Cr.CAP()) == True{} : Bool}) -> LALogic.pc.G(c, dead, Cr.finish.fail(b, c, i, Cr.Every{q}, nx, 1n+k, Nil{}, ss, Cr.MLoss{} <> h)):
  match b:
    case True{}:
      (Unit{}, (Unit{}, (h3, (pc.top_fail(ss, c, nx, 1n+k, h4), (Unit{}, ((Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), eqb), Unit{}))))))
    case False{}:
      (Unit{}, (Unit{}, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (Unit{}, ((Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), LANat.pc.lt_succ_le(k, Cr.CAP(), lt)), Unit{}))))))

def pc.cnt_fin(+o: Cr.Out, +k: Nat, +h: List<&2, Cr.Mark>, c6: LALogic.pc.Cnt(Cr.Active{}, k, h)) -> LALogic.pc.Cnt(Cr.Finished{}, Cr.count.streak(o, k), Cr.count.hist(o, h)):
  match o:
    case Cr.Win{}:
      ({==}, {==})
    case Cr.Loss{}:
      (ek, lt) = c6
      (Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), LANat.pc.lt_succ_le(k, Cr.CAP(), lt))
    case Cr.Skip{}:
      (ek, lt) = c6
      (ek, LANat.pc.lt_le(k, Cr.CAP(), lt))

def pc.fin_count(+s: Cr.Sched, +o: Cr.Out, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, h3: Cr.Desc(ss), h4: LALogic.pc.Top(ss, c, nx), h5: LALogic.pc.OnceG(s, ss, nx), h6: LALogic.pc.Cnt(Cr.Active{}, k, h)) -> LALogic.pc.G(c, dead, Cr.finish.count(Cr.is_once(s), c, o, i, s, nx, k, Nil{}, ss, h)):
  match s:
    case Cr.Once{+d}:
      (Unit{}, (Unit{}, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (LALogic.pc.once_none(Cr.Once{d}, ss, nx, h5), (pc.cnt_fin(o, k, h, h6), {==}))))))
    case Cr.Every{+q}:
      match o:
        case Cr.Win{}:
          (Unit{}, (Unit{}, (h3, (h4, (Unit{}, (({==}, {==}), Unit{}))))))
        case Cr.Skip{}:
          (Unit{}, (Unit{}, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (h6, Unit{}))))))
        case Cr.Loss{}:
          (ek, lt) = h6
          pc.fin_fail(Nat.is_lt(1n+k, Cr.CAP()), c, dead, i, q, nx, k, ss, h, {==}, h3, h4, ek, lt)

def pc.fin_st(+st: Cr.Status, +x: Cr.Claim, +c: Nat, +dead: List<&2, Nat>, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, h3: Cr.Desc(ss), h4: LALogic.pc.Top(ss, c, nx), h5: LALogic.pc.OnceG(s, ss, nx), h6: LALogic.pc.Cnt(st, k, h)) -> LALogic.pc.G(c, dead, Cr.finish.own(True{}, x, c, o, i, s, st, nx, k, Nil{}, ss, h)):
  match st:
    case Cr.Active{}:
      pc.fin_count(s, o, c, dead, i, nx, k, ss, h, h3, h4, h5, h6)
    case Cr.Paused{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Paused{})))))))
    case Cr.Finished{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Finished{})))))))
    case Cr.Cancelled{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Cancelled{})))))))

# the run of p is its claim's: releasing it leaves no run
def pc.fin_run(b: Bool, +rs: List<&2, Nat>, +cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eq: {Cr.has(p, rs) == b : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, rs, ss, h})) -> LALogic.pc.G(c, dead, Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match rs:
        case Nil{}:
          LALogic.cron.pc.absurdF(LALogic.pc.G(c, dead, Cr.finish.run(True{}, p, c, o, i, s, st, nx, k, cl, Nil{}, ss, h)), eq)
        case +w <> +t:
          match t:
            case +y <> +u:
              (h1, g2) = g
              match h1:
            case Nil{}:
              match cl:
                case None{}:
                  (h1, g2) = g
                  match h1:
                case Some{+x}:
                  match x:
                    case Cr.Claim{+xo, +w2}:
                      (h1, g2) = g
                      (h2, g3) = g2
                      (h3, g4) = g3
                      (h4, g5) = g4
                      (h5, g6) = g5
                      (h6, h7) = g6
                      +ewp = LALogic.cron.pc.eq_of(w, p, LALogic.cron.pc.or_false_r(Nat.is_eq(w, p), eq))
                      +w2p = Equal.trans(Nat, w2, w, p, h1, ewp)
                      %Equal.sym(Nat, w2, p, w2p) : LALogic.pc.G(c, dead, Cr.finish.own(Nat.is_eq(_, p), Cr.Claim{xo, _}, c, o, i, s, st, nx, k, Cr.drop(p, [w]), ss, h))
                      %Equal.sym(Nat, w, p, ewp) : LALogic.pc.G(c, dead, Cr.finish.own(Nat.is_eq(p, p), Cr.Claim{xo, p}, c, o, i, s, st, nx, k, Cr.drop.put(Nat.is_eq(_, p), _, Nil{}), ss, h))
                      %Equal.sym(Bool, Nat.is_eq(p, p), True{}, LANat.cron.pc.eq_refl(p)) : LALogic.pc.G(c, dead, Cr.finish.own(_, Cr.Claim{xo, p}, c, o, i, s, st, nx, k, Cr.drop.put(_, p, Nil{}), ss, h))
                      pc.fin_st(st, Cr.Claim{xo, p}, c, dead, o, i, s, nx, k, ss, h, h3, h4, h5, h6)

def pc.g_finish(+p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.finish(p, c, o, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      pc.fin_run(Cr.has(p, rs), rs, cl, p, c, o, dead, i, s, st, nx, k, ss, h, {==}, g)

def pc.pick_fin(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.job.pick(b, Cr.finish(p, c, o, j), j)):
  match b:
    case True{}:
      pc.g_finish(p, c, o, dead, j, g)
    case False{}:
      g

# User actions keep the invariant
# -------------------------------

def pc.g_cancel(+c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.cancel(j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Cancelled{}:
          g
        case Cr.Active{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (LALogic.pc.once_none(s, ss, nx, h5), (LANat.pc.cnt_down(Cr.Cancelled{}, k, h, h6), pc.ends_cancel(s, rs)))))))
        case Cr.Paused{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (LALogic.pc.once_none(s, ss, nx, h5), (h6, pc.ends_cancel(s, rs)))))))
        case Cr.Finished{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (LALogic.pc.top_none(ss, c, nx, h4), (LALogic.pc.once_none(s, ss, nx, h5), (h6, pc.ends_cancel(s, rs)))))))

def pc.pick_cancel(b: Bool, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.job.pick(b, Cr.cancel(j), j)):
  match b:
    case True{}:
      pc.g_cancel(c, dead, j, g)
    case False{}:
      g

def pc.g_resume(+c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.resume(c, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match s:
        case Cr.Once{+d}:
          g
        case Cr.Every{+q}:
          match st:
            case Cr.Active{}:
              (h1, g2) = g
              (h2, g3) = g2
              (h3, g4) = g3
              (h4, g5) = g4
              (h1, (h2, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (({==}, {==}), Unit{}))))))
            case Cr.Paused{}:
              (h1, g2) = g
              (h2, g3) = g2
              (h3, g4) = g3
              (h4, g5) = g4
              (h1, (h2, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (({==}, {==}), Unit{}))))))
            case Cr.Finished{}:
              g
            case Cr.Cancelled{}:
              g

def pc.pick_resume(b: Bool, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.job.pick(b, Cr.resume(c, j), j)):
  match b:
    case True{}:
      pc.g_resume(c, dead, j, g)
    case False{}:
      g

def pc.abort_one(b: Bool, +w: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, g: LALogic.pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, [w], ss, h})) -> LALogic.pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, Cr.drop.put(b, w, Nil{}), ss, h}):
  match b:
    case True{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, st)))))))
    case False{}:
      g

def pc.g_abort(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, dead, Cr.unrun(p, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match rs:
        case Nil{}:
          g
        case +w <> +t:
          match t:
            case Nil{}:
              pc.abort_one(Nat.is_eq(w, p), w, c, dead, i, s, st, nx, k, cl, ss, h, g)
            case +y <> +u:
              (h1, g2) = g
              match h1:

def pc.die_one(b: Bool, +w: Nat, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eqb: {Nat.is_eq(w, p) == b : Bool}, g: LALogic.pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, [w], ss, h})) -> LALogic.pc.G(c, p <> dead, Cr.Job{i, s, st, nx, k, cl, Cr.drop.put(b, w, Nil{}), ss, h}):
  match b:
    case True{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, st)))))))
    case False{}:
      (h1, g2) = g
      (h2, g3) = g2
      (live, un) = h2
      (h1, ((LABool.pc.or_ff(Nat.is_eq(p, w), Cr.has(w, dead), LANat.pc.eq_flip(w, p, eqb), live), Unit{}), g3))

def pc.g_die(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, p <> dead, Cr.unrun(p, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match rs:
        case Nil{}:
          (h1, g2) = g
          (h2, g3) = g2
          (Unit{}, (Unit{}, g3))
        case +w <> +t:
          match t:
            case Nil{}:
              pc.die_one(Nat.is_eq(w, p), w, p, c, dead, i, s, st, nx, k, cl, ss, h, {==}, g)
            case +y <> +u:
              (h1, g2) = g
              match h1:

def pc.g_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +al: LALogic.pc.Alive(e, dead), g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(c, LALogic.pc.dead_after(e, dead), Cr.job(e, c, dead, j)):
  match e:
    case Cr.Take{+p}:
      pc.g_take(p, c, dead, j, al, g)
    case Cr.Recover{+p}:
      pc.g_recover(p, dead, c, j, g)
    case Cr.Finish{+p, +i, +o}:
      pc.pick_fin(Nat.is_eq(Cr.Job.id(j), i), p, c, o, dead, j, g)
    case Cr.Abort{+p}:
      pc.g_abort(p, c, dead, j, g)
    case Cr.Die{+p}:
      pc.g_die(p, c, dead, j, g)
    case Cr.Cancel{+p, +i}:
      pc.pick_cancel(Nat.is_eq(Cr.Job.id(j), i), c, dead, j, g)
    case Cr.Resume{+p, +i}:
      pc.pick_resume(Nat.is_eq(Cr.Job.id(j), i), c, dead, j, g)
    case Cr.Create{p, s}:
      g
    case Cr.Tick{d}:
      g
    case Cr.RawJob{t}:
      g
    case Cr.RawClaim{t}:
      g
    case Cr.Corrupt{t}:
      g

def pc.all_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +al: LALogic.pc.Alive(e, dead), g: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.AllG(c, LALogic.pc.dead_after(e, dead), Cr.recs(e, c, dead, rs)):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_job(e, c, dead, j, al, a), pc.all_recs(e, c, dead, t, al, b))
        case Cr.Raw{x}:
          pc.all_recs(e, c, dead, t, al, g)

def pc.g_new(+c: Nat, +dead: List<&2, Nat>, +n: Nat, +sc: Cr.Sched) -> LALogic.pc.G(c, dead, Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}):
  (Unit{}, (Unit{}, (Unit{}, (Unit{}, (LALogic.pc.once_empty(sc, Some{Cr.first(sc, c)}), (({==}, {==}), pc.ends_active(sc, Nil{})))))))

def pc.alive_create(b: Bool, +c: Nat, +dead: List<&2, Nat>, +n: Nat, +sc: Cr.Sched, +rs: List<&2, Cr.Rec>, -bad: Maybe<&2, Nat>, -rd: List<&2, Nat>, -aside: List<&2, Nat>, inv: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.Inv(Cr.step.alive(b, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match b:
    case False{}:
      LAList.pc.all_append(c, dead, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}], inv, (pc.g_new(c, dead, n, sc), Unit{}))
    case True{}:
      inv

def pc.alive_take(b: Bool, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -b1: Maybe<&2, Nat>, -rd1: List<&2, Nat>, -n1: Nat, -a1: List<&2, Nat>, -b0: Maybe<&2, Nat>, -rd0: List<&2, Nat>, -n0: Nat, -a0: List<&2, Nat>, eqb: {Cr.has(p, dead) == b : Bool}, inv: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.Inv(Cr.step.alive(b, Cr.S{b1, Cr.recs(Cr.Take{p}, c, dead, rs), rd1, dead, c, n1, a1}, Cr.S{b0, rs, rd0, dead, c, n0, a0})):
  match b:
    case False{}:
      pc.all_recs(Cr.Take{p}, c, dead, rs, eqb, inv)
    case True{}:
      inv

def pc.alive_recs(b: Bool, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -b1: Maybe<&2, Nat>, -rd1: List<&2, Nat>, -n1: Nat, -a1: List<&2, Nat>, -b0: Maybe<&2, Nat>, -rd0: List<&2, Nat>, -n0: Nat, -a0: List<&2, Nat>, +al: LALogic.pc.Alive(e, dead), de: {LALogic.pc.dead_after(e, dead) == dead : List<&2, Nat>}, inv: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.Inv(Cr.step.alive(b, Cr.S{b1, Cr.recs(e, c, dead, rs), rd1, dead, c, n1, a1}, Cr.S{b0, rs, rd0, dead, c, n0, a0})):
  match b:
    case False{}:
      %de : LALogic.pc.AllG(c, _, Cr.recs(e, c, dead, rs))
      pc.all_recs(e, c, dead, rs, al, inv)
    case True{}:
      inv

def pc.raw_job(bad: Maybe<&2, Nat>, +t: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -rd: List<&2, Nat>, -n: Nat, -aside: List<&2, Nat>, inv: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.Inv(Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      LAList.pc.all_append(c, dead, rs, [Cr.Raw{t}], inv, Unit{})
    case Some{x}:
      inv

def pc.raw_claim(bad: Maybe<&2, Nat>, +t: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -rd: List<&2, Nat>, -n: Nat, -aside: List<&2, Nat>, inv: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.Inv(Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      inv
    case Some{x}:
      inv

def pc.inv_step(s: Cr.S, +e: Cr.Ev, inv: LALogic.pc.Inv(s)) -> LALogic.pc.Inv(Cr.step(s, e)):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          pc.alive_create(Cr.has(p, dead), c, dead, n, sc, rs, bad, rd, aside, inv)
        case Cr.Take{+p}:
          pc.alive_take(Cr.has(p, dead), p, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, {==}, inv)
        case Cr.Recover{+p}:
          pc.alive_recs(Cr.has(p, dead), Cr.Recover{p}, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Finish{+p, +i, +o}:
          pc.alive_recs(Cr.has(p, dead), Cr.Finish{p, i, o}, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Abort{+p}:
          pc.alive_recs(Cr.has(p, dead), Cr.Abort{p}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Die{+p}:
          pc.all_recs(Cr.Die{p}, c, dead, rs, Unit{}, inv)
        case Cr.Cancel{+p, +i}:
          pc.alive_recs(Cr.has(p, dead), Cr.Cancel{p, i}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Resume{+p, +i}:
          pc.alive_recs(Cr.has(p, dead), Cr.Resume{p, i}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Tick{+d}:
          LANat.pc.all_tick(c, d, dead, rs, inv)
        case Cr.RawJob{+t}:
          pc.raw_job(bad, t, c, dead, rs, rd, n, aside, inv)
        case Cr.RawClaim{+t}:
          pc.raw_claim(bad, t, c, dead, rs, rd, n, aside, inv)
        case Cr.Corrupt{t}:
          Unit{}

def pc.inv_go(evs: List<&2, Cr.Ev>, +s: Cr.S, inv: LALogic.pc.Inv(s)) -> LALogic.pc.Inv(Cr.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pc.inv_go(rest, Cr.step(s, e), pc.inv_step(s, e, inv))

def pc.inv_run(evs: List<&2, Cr.Ev>) -> LALogic.pc.Inv(Cr.run(evs)):
  pc.inv_go(evs, Cr.S.empty(), Unit{})

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
