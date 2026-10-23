# eukhe: lemmas the proofs of area compactor share

import Base
import ../../bend/optchat.bend as O
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws
import ../base.bend as L

def pc.lt_succ_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      L.pc.absurd_ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_succ_of_le(p, q, e)

def pc.le_succ_of_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      L.pc.lt_zero({Nat.is_le(1n+p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      L.compactor.pc.le_zero(q)
    case 1n+p 1n+q:
      pc.le_succ_of_lt(p, q, e)

def pc.lt_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.lt_add_l(p, x, y, e)

def pc.le_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.le_add_l(p, x, y, e)

def pc.and_true(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      L.pc.absurd_ft({False{} == True{} : Bool}, ea)

def pc.lt_self(+x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  pc.lt_succ_of_le(x, x, L.compactor.pc.le_refl(x))

# an outcome that counts lowers a pending line's weight
def pc.after_falls(n: Nat, o: C.Outcome, +m: Nat, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      pc.lt_succ_of_le(m, Nat.add(p, m), L.compactor.pc.le_add(p, m))
    case 0n C.Failed{}:
      pc.lt_self(m)
    case 1n+p C.Failed{}:
      pc.lt_self(Nat.add(p, m))
    case p C.Disk{}:
      L.pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Disk{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)
    case p C.Stopped{}:
      L.pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Stopped{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)

# and no outcome raises it
def pc.after_holds(n: Nat, o: C.Outcome, +m: Nat) -> {Nat.is_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      L.pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Built{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Built{}, m, {==}))
    case +p C.Failed{}:
      L.pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Failed{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Failed{}, m, {==}))
    case 0n C.Disk{}:
      L.compactor.pc.le_refl(1n+m)
    case 1n+p C.Disk{}:
      L.compactor.pc.le_refl(Nat.add(2n+p, m))
    case 0n C.Stopped{}:
      L.compactor.pc.le_refl(1n+m)
    case 1n+p C.Stopped{}:
      L.compactor.pc.le_refl(Nat.add(2n+p, m))

def pc.settle_falls(ps: List<&2, C.Pend>, k: Nat, o: C.Outcome, due: {C.pending_at(ps, k) == True{} : Bool}, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      L.pc.absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, due)
    case C.Made{} <> rest 0n:
      L.pc.absurd_ft({Nat.is_lt(C.measure(rest), C.measure(rest)) == True{} : Bool}, due)
    case C.Owed{n} <> rest 0n:
      pc.after_falls(n, o, C.measure(rest), lands)
    case p <> rest 1n+j:
      pc.lt_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_falls(rest, j, o, due, lands))

def pc.settle_holds(ps: List<&2, C.Pend>, k: Nat, +o: C.Outcome) -> {Nat.is_le(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      {==}
    case C.Made{} <> rest 0n:
      L.compactor.pc.le_refl(C.measure(rest))
    case C.Owed{+n} <> rest 0n:
      pc.after_holds(n, o, C.measure(rest))
    case +p <> rest 1n+j:
      pc.le_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_holds(rest, j, o))

def pc.bounded_step(b: Bool, +h: Nat, +x: Nat, +m1: Nat, +m0: Nat, +ih: {Nat.is_le(Nat.add(h, x), m1) == True{} : Bool}, holds: {Nat.is_le(m1, m0) == True{} : Bool}, falls: {b == True{} : Bool} -> {Nat.is_lt(m1, m0) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(O.bit(b, 0n), h), x), m0) == True{} : Bool}:
  match b:
    case False{}:
      L.compactor.pc.le_trans(Nat.add(h, x), m1, m0, ih, holds)
    case True{}:
      pc.le_succ_of_lt(Nat.add(h, x), m0, L.pc.le_lt_trans(Nat.add(h, x), m1, m0, ih, falls({==})))

def pc.settle_bounded(es: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}:
  match es:
    case Nil{}:
      L.compactor.pc.le_refl(C.measure(ps))
    case C.End{+k, +o} <> +rest:
      +next = C.hit(ps, k, o)
      +due = C.pending_at(ps, k)
      +lands = C.Outcome.lands(o)
      pc.bounded_step(Bool.and(due, lands), C.hits(rest, next), C.measure(C.run(rest, next)), C.measure(next), C.measure(ps), pc.settle_bounded(rest, next), pc.settle_holds(ps, k, o), +both => pc.settle_falls(ps, k, o, L.pf.and_l(due, lands, both), L.pf.and_r(due, lands, both)))

# (H2) Need first
# ---------------

def pc.needed_cons(+info: O.Info, +h: O.Node, +v: List<&2, O.Node>, ns: List<&2, O.Node>, +e: {C.needed(info, v, ns) == True{} : Bool}) -> {C.needed(info, h <> v, ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> rest:
      +a = Bool.and(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)))
      +ea = L.pf.and_l(a, C.needed(info, v, rest), e)
      pc.and_true(Bool.and(Bool.or(O.Node.eq(h, n), O.Nodes.has(v, n)), Bool.not(O.Info.built(info, n))), C.needed(info, h <> v, rest), pc.and_true(Bool.or(O.Node.eq(h, n), O.Nodes.has(v, n)), Bool.not(O.Info.built(info, n)), L.pf.or_r(O.Node.eq(h, n), O.Nodes.has(v, n), L.pf.and_l(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)), ea)), L.pf.and_r(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)), ea)), pc.needed_cons(info, h, v, rest, L.pf.and_r(a, C.needed(info, v, rest), e)))

def pc.emit_ok(stop: Bool, b: Bool, free: Bool, +info: O.Info, +h: O.Node, +rest: List<&2, O.Node>, +rec: List<&2, O.Node>, eb: {b == O.Info.built(info, h) : Bool}, +ih: {C.needed(info, rest, rec) == True{} : Bool}) -> {C.needed(info, h <> rest, O.cand.emit(stop, b, free, h, rec)) == True{} : Bool}:
  match stop b free:
    case True{} y z:
      {==}
    case False{} True{} z:
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} True{}:
      %eb : {Bool.and(Bool.and(Bool.or(O.Node.eq(h, h), O.Nodes.has(rest, h)), Bool.not(_)), C.needed(info, h <> rest, rec)) == True{} : Bool}
      %L.pf.node_eq_refl(h) : {Bool.and(Bool.and(Bool.or(_, O.Nodes.has(rest, h)), True{}), C.needed(info, h <> rest, rec)) == True{} : Bool}
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} False{}:
      pc.needed_cons(info, h, rest, rec, ih)

def pc.cand_ok(v: List<&2, O.Node>, +info: O.Info, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, room: Nat) -> {C.needed(info, v, O.cand.view(v, info, busy, jobs, unb, room)) == True{} : Bool}:
  match v room:
    case Nil{} r:
      {==}
    case h <> rest 0n:
      {==}
    case +h <> +rest 1n+r:
      +unb2 = Nat.add(unb, O.bit(Bool.not(O.Info.built(info, h)), 0n))
      +room2 = Nat.sub(1n+r, O.bit(Bool.and(Bool.not(O.Info.built(info, h)), Bool.not(O.Nodes.has(busy, h))), 0n))
      pc.emit_ok(Nat.is_ge(unb, jobs), O.Info.built(info, h), Bool.not(O.Nodes.has(busy, h)), info, h, rest, O.cand.view(rest, info, busy, jobs, unb2, room2), {==}, pc.cand_ok(rest, info, busy, jobs, unb2, room2))

def pc.need_first(+cfg: O.Cfg, +s: O.St) -> {C.needed(O.St.info(s), O.St.view(s), O.cands.need(cfg, s)) == True{} : Bool}:
  pc.cand_ok(O.St.view(s), O.St.info(s), O.St.busy(s), O.Cfg.jobs(cfg), 0n, Nat.sub(O.Cfg.jobs(cfg), List.length(&2, O.Node, O.St.busy(s))))
