# eukhe: the proof of LAW need_progress

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_le.bend as LNatIsLe
import ../base/nat/is_lt.bend as LNatIsLt
import ./base.bend as LA

# (H2) Progress
# -------------
# The queue scans the view oldest first and stops after jobs unbuilt
# lines. A line the scan passes is built, or busy: then a call of the
# busy list starts at it, and the view's lines start in order, so that
# call starts before every later line. pc.ahead(s, busy), the busy calls
# that start at s or later, plus the unbuilt lines passed stays below
# jobs: the scan reaches a line that is neither built nor busy.

def pc.add_zero(n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pc.add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def pc.le_add_r(a: Nat, c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      LNatIsLe.compactor.pc.le_zero(c)
    case 1n+p:
      pc.le_add_r(p, c)

def pc.lt_add_pos(a: Nat, c: Nat, pos: {O.Nat.is_pos(c) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          pos
        case 1n+q:
          {==}
    case 1n+p:
      pc.lt_add_pos(p, c, pos)

def pc.double_pos(x: Nat, e: {O.Nat.is_pos(x) == True{} : Bool}) -> {O.Nat.is_pos(Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      e
    case 1n+p:
      {==}

def pc.pow2_pos(+l: Nat) -> {O.Nat.is_pos(O.pow2(l)) == True{} : Bool}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      pc.double_pos(O.pow2(p), pc.pow2_pos(p))

# every line covers a message
def pc.count_pos(n: O.Node) -> {O.Nat.is_pos(O.Node.count(n)) == True{} : Bool}:
  match n:
    case O.Node{l, i}:
      pc.pow2_pos(l)

def pc.le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n q:
      LNatIsLe.compactor.pc.le_trans(c, d, Nat.add(q, d), cd, LNatIsLe.compactor.pc.le_add(q, d))
    case 1n+p 0n:
      LBoolMisc.pc.absurd_ft({Nat.is_le(Nat.add(1n+p, c), d) == True{} : Bool}, ab)
    case 1n+p 1n+q:
      pc.le_add_both(p, q, c, d, ab, cd)

def pc.bit_le(x: Bool, y: Bool, imp: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Nat.is_le(O.bit(x, 0n), O.bit(y, 0n)) == True{} : Bool}:
  match x y:
    case False{} z:
      LNatIsLe.compactor.pc.le_zero(O.bit(z, 0n))
    case True{} True{}:
      {==}
    case True{} False{}:
      LBoolMisc.pc.absurd_ft({Nat.is_le(1n, 0n) == True{} : Bool}, imp({==}))

def pc.bit_le_one(x: Bool) -> {Nat.is_le(O.bit(x, 0n), 1n) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def pc.not_false(x: Bool, e: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.pc.absurd_tf({False{} == True{} : Bool}, e)

def pc.lt_not_ge(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_ge(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LBoolMisc.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_ge(p, q, e)

def pc.sub_pos(b: Nat, j: Nat, e: {Nat.is_lt(b, j) == True{} : Bool}) -> {O.Nat.is_pos(Nat.sub(j, b)) == True{} : Bool}:
  match b j:
    case p 0n:
      LNatIsLt.pc.lt_zero({O.Nat.is_pos(Nat.sub(0n, p)) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.sub_pos(p, q, e)

# equal nodes start together
def pc.same_eq(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {O.Bits.same(xs, ys) == True{} : Bool}) -> {Nat.is_eq(O.Bits.val(xs), O.Bits.val(ys)) == True{} : Bool}:
  %LA.pa.cmp_val(xs, ys) : {Cmp.is_eq(_) == True{} : Bool}
  e

def pc.eq_start(a: O.Node, b: O.Node, +e: {O.Node.eq(a, b) == True{} : Bool}) -> {O.Node.start(a) == O.Node.start(b) : Nat}:
  match a b:
    case O.Node{+la, +ia} O.Node{+lb, +ib}:
      %LA.cover.eq_of_is_eq(la, lb, LBoolAnd.pf.and_l(Nat.is_eq(la, lb), O.Bits.same(ia, ib), e)) : {O.shl(la, O.Bits.val(ia)) == O.shl(_, O.Bits.val(ib)) : Nat}
      %LA.cover.eq_of_is_eq(O.Bits.val(ia), O.Bits.val(ib), pc.same_eq(ia, ib, LBoolAnd.pf.and_r(Nat.is_eq(la, lb), O.Bits.same(ia, ib), e))) : {O.shl(la, O.Bits.val(ia)) == O.shl(la, _) : Nat}
      {==}

# the busy calls that start at s or later
def pc.ahead(+s: Nat, bs: List<&2, O.Node>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      Nat.add(O.bit(Nat.is_le(s, O.Node.start(b)), 0n), pc.ahead(s, rest))

def pc.ahead_len(+s: Nat, bs: List<&2, O.Node>) -> {Nat.is_le(pc.ahead(s, bs), List.length(&2, O.Node, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.le_add_both(O.bit(Nat.is_le(s, O.Node.start(b)), 0n), 1n, pc.ahead(s, rest), List.length(&2, O.Node, rest), pc.bit_le_one(Nat.is_le(s, O.Node.start(b))), pc.ahead_len(s, rest))

def pc.ahead_mono(bs: List<&2, O.Node>, +s: Nat, +s2: Nat, +le: {Nat.is_le(s, s2) == True{} : Bool}) -> {Nat.is_le(pc.ahead(s2, bs), pc.ahead(s, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +sb = O.Node.start(b)
      pc.le_add_both(O.bit(Nat.is_le(s2, sb), 0n), O.bit(Nat.is_le(s, sb), 0n), pc.ahead(s2, rest), pc.ahead(s, rest), pc.bit_le(Nat.is_le(s2, sb), Nat.is_le(s, sb), z => LNatIsLe.compactor.pc.le_trans(s, s2, sb, le, z)), pc.ahead_mono(rest, s, s2, le))

def pc.drop_step(x: Bool, -y: Bool, +s: Nat, +s2: Nat, +sb: Nat, +a1: Nat, +a2: Nat, lt: {Nat.is_lt(s, s2) == True{} : Bool}, has: {Bool.or(x, y) == True{} : Bool}, at: {x == True{} : Bool} -> {s == sb : Nat}, mono: {Nat.is_le(a2, a1) == True{} : Bool}, ih: {y == True{} : Bool} -> {Nat.is_le(1n+a2, a1) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(O.bit(Nat.is_le(s2, sb), 0n), a2), Nat.add(O.bit(Nat.is_le(s, sb), 0n), a1)) == True{} : Bool}:
  match x:
    case True{}:
      %at({==}) : {Nat.is_le(1n+Nat.add(O.bit(Nat.is_le(s2, _), 0n), a2), Nat.add(O.bit(Nat.is_le(s, _), 0n), a1)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s2, s), False{}, LNatIsLe.pc.lt_not_le(s, s2, lt)) : {Nat.is_le(1n+Nat.add(O.bit(_, 0n), a2), Nat.add(O.bit(Nat.is_le(s, s), 0n), a1)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s, s), True{}, LNatIsLe.compactor.pc.le_refl(s)) : {Nat.is_le(1n+Nat.add(O.bit(False{}, 0n), a2), Nat.add(O.bit(_, 0n), a1)) == True{} : Bool}
      mono
    case False{}:
      +x2 = O.bit(Nat.is_le(s2, sb), 0n)
      +x1 = O.bit(Nat.is_le(s, sb), 0n)
      %Equal.sym(Nat, 1n+Nat.add(x2, a2), Nat.add(x2, 1n+a2), LA.cover.add_succ(x2, a2)) : {Nat.is_le(_, Nat.add(x1, a1)) == True{} : Bool}
      pc.le_add_both(x2, x1, 1n+a2, a1, pc.bit_le(Nat.is_le(s2, sb), Nat.is_le(s, sb), z => LNatIsLe.compactor.pc.le_trans(s, s2, sb, LNatIsLt.pc.lt_to_le(s, s2, lt), z)), ih(has))

# a busy call at s drops out of the calls ahead once the scan is past s
def pc.ahead_drop(bs: List<&2, O.Node>, +h: O.Node, +s: Nat, +s2: Nat, +lt: {Nat.is_lt(s, s2) == True{} : Bool}, +st: {O.Node.start(h) == s : Nat}, has: {O.Nodes.has(bs, h) == True{} : Bool}) -> {Nat.is_le(1n+pc.ahead(s2, bs), pc.ahead(s, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      LBoolMisc.pc.absurd_ft({Nat.is_le(1n, 0n) == True{} : Bool}, has)
    case +b <> +rest:
      pc.drop_step(O.Node.eq(b, h), O.Nodes.has(rest, h), s, s2, O.Node.start(b), pc.ahead(s, rest), pc.ahead(s2, rest), lt, has, e => Equal.sym(Nat, O.Node.start(b), s, Equal.trans(Nat, O.Node.start(b), O.Node.start(h), s, pc.eq_start(b, h, e), st)), pc.ahead_mono(rest, s, s2, LNatIsLt.pc.lt_to_le(s, s2, lt)), hr => pc.ahead_drop(rest, h, s, s2, lt, st, hr))

def pc.under_built(+a1: Nat, +a2: Nat, +unb: Nat, +jobs: Nat, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, mono: {Nat.is_le(a2, a1) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, 0n)), jobs) == True{} : Bool}:
  %pc.add_zero(unb) : {Nat.is_lt(Nat.add(a2, _), jobs) == True{} : Bool}
  LNatIsLt.pc.le_lt_trans(Nat.add(a2, unb), Nat.add(a1, unb), jobs, pc.le_add_both(a2, a1, unb, unb, mono, LNatIsLe.compactor.pc.le_refl(unb)), under)

def pc.under_busy(+a1: Nat, +a2: Nat, +unb: Nat, +jobs: Nat, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, drop: {Nat.is_le(1n+a2, a1) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, 1n)), jobs) == True{} : Bool}:
  %LA.cover.add_one(unb) : {Nat.is_lt(Nat.add(a2, _), jobs) == True{} : Bool}
  %LA.cover.add_succ(a2, unb) : {Nat.is_lt(_, jobs) == True{} : Bool}
  LNatIsLt.pc.le_lt_trans(1n+Nat.add(a2, unb), Nat.add(a1, unb), jobs, pc.le_add_both(1n+a2, a1, unb, unb, drop, LNatIsLe.compactor.pc.le_refl(unb)), under)

# one line of the scan: a built line passes, a free one starts, a busy
# one passes and its call drops out of the calls ahead
def pc.scan_step(stop: Bool, b: Bool, f: Bool, +info: O.Info, +h: O.Node, +rest: List<&2, O.Node>, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, +r: Nat, +a1: Nat, +a2: Nat, estop: {stop == False{} : Bool}, idle: {Bool.or(Bool.and(Bool.not(b), f), C.idle(info, rest, busy)) == True{} : Bool}, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, mono: {Nat.is_le(a2, a1) == True{} : Bool}, drop: {f == False{} : Bool} -> {Nat.is_le(1n+a2, a1) == True{} : Bool}, ih: {C.idle(info, rest, busy) == True{} : Bool} -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, O.bit(Bool.not(b), 0n))), jobs) == True{} : Bool} -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.view(rest, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(b), 0n)), 1n+r))) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.emit(stop, b, f, h, O.cand.view(rest, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(b), 0n)), Nat.sub(1n+r, O.bit(Bool.and(Bool.not(b), f), 0n)))))) == True{} : Bool}:
  match stop b f:
    case True{} y z:
      LBoolMisc.pc.absurd_tf({False{} == True{} : Bool}, estop)
    case False{} True{} z:
      ih(idle, pc.under_built(a1, a2, unb, jobs, under, mono))
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      ih(idle, pc.under_busy(a1, a2, unb, jobs, under, drop({==})))

def pc.scan(v: List<&2, O.Node>, +room: Nat, +info: O.Info, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, +s: Nat, -e: Nat, tiles: S.Tiles(s, v, e), idle: {C.idle(info, v, busy) == True{} : Bool}, pos: {O.Nat.is_pos(room) == True{} : Bool}, +under: {Nat.is_lt(Nat.add(pc.ahead(s, busy), unb), jobs) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.view(v, info, busy, jobs, unb, room))) == True{} : Bool}:
  match v room:
    case Nil{} k:
      idle
    case h <> rest 0n:
      pos
    case +h <> +rest 1n+r:
      (st, tl) = tiles
      +s2 = Nat.add(s, O.Node.count(h))
      +a1 = pc.ahead(s, busy)
      +a2 = pc.ahead(s2, busy)
      pc.scan_step(Nat.is_ge(unb, jobs), O.Info.built(info, h), Bool.not(O.Nodes.has(busy, h)), info, h, rest, busy, jobs, unb, r, a1, a2, pc.lt_not_ge(unb, jobs, LNatIsLt.pc.le_lt_trans(unb, Nat.add(a1, unb), jobs, LNatIsLe.compactor.pc.le_add(a1, unb), under)), idle, under, pc.ahead_mono(busy, s, s2, pc.le_add_r(s, O.Node.count(h))), nf => pc.ahead_drop(busy, h, s, s2, pc.lt_add_pos(s, O.Node.count(h), pc.count_pos(h)), st, pc.not_false(O.Nodes.has(busy, h), nf)), i => u => pc.scan(rest, 1n+r, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(O.Info.built(info, h)), 0n)), s2, e, tl, i, {==}, u))

def pc.under0(+jobs: Nat, +busy: List<&2, O.Node>, room: {Nat.is_lt(List.length(&2, O.Node, busy), jobs) == True{} : Bool}) -> {Nat.is_lt(Nat.add(pc.ahead(0n, busy), 0n), jobs) == True{} : Bool}:
  %pc.add_zero(pc.ahead(0n, busy)) : {Nat.is_lt(_, jobs) == True{} : Bool}
  LNatIsLt.pc.le_lt_trans(pc.ahead(0n, busy), List.length(&2, O.Node, busy), jobs, pc.ahead_len(0n, busy), room)

def pc.need_progress(+cfg: O.Cfg, +evs: List<&2, O.Ev>, +room: {Nat.is_lt(List.length(&2, O.Node, O.St.busy(O.run(cfg, evs))), O.Cfg.jobs(cfg)) == True{} : Bool}, idle: {C.idle(O.St.info(O.run(cfg, evs)), O.St.view(O.run(cfg, evs)), O.St.busy(O.run(cfg, evs))) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cands.need(cfg, O.run(cfg, evs)))) == True{} : Bool}:
  +s = O.run(cfg, evs)
  +jobs = O.Cfg.jobs(cfg)
  +busy = O.St.busy(s)
  pc.scan(O.St.view(s), Nat.sub(jobs, List.length(&2, O.Node, busy)), O.St.info(s), busy, jobs, 0n, 0n, S.total.of(cfg, evs), LA.view_covers(cfg, evs), idle, pc.sub_pos(List.length(&2, O.Node, busy), jobs, room), pc.under0(jobs, busy, room))

def Optchat.need_progress(cfg, evs, room, idle):
  pc.need_progress(cfg, evs, room, idle)
