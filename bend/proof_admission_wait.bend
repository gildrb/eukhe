# proof_admission_wait: the interactive bound of LAWS.bend (rule H3.4 of
# docs/harness.md). An interactive waiter w waits for ahead(s, w): the
# interactive slots held and the interactive waiters older than w. No op
# raises it, a release of an interactive slot lowers it by one, and
# while w waits it is at least one (no lost wake-up). So w is granted
# after at most ahead(s, w) interactive releases, whatever background
# requests do.

import Base
import ./admission.bend as A
import ./proof_admission.bend as P

# Numbers
# -------

def aw.le_succ(x: Nat, +y: Nat, e: {A.le(x, y) == True{} : Bool}) -> {A.le(x, 1n+y) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+a:
      match y:
        case 0n:
          P.ad.absurd({A.le(1n+a, 1n) == True{} : Bool}, e)
        case 1n+b:
          aw.le_succ(a, b, e)

def aw.le0(a: Nat, e: {A.le(a, 0n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+x:
      P.ad.absurd({1n+x == 0n : Nat}, e)

def aw.bit_mono(b: Bool, -x: Nat, -y: Nat, e: {A.le(x, y) == True{} : Bool}) -> {A.le(A.bit(b, x), A.bit(b, y)) == True{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      e

def aw.bit_or(a: Bool, b: Bool, +y: Nat) -> {A.le(A.bit(a, y), A.bit(Bool.or(a, b), y)) == True{} : Bool}:
  match a b:
    case True{} _:
      P.ad.le_refl(y)
    case False{} True{}:
      aw.le_succ(y, y, P.ad.le_refl(y))
    case False{} False{}:
      P.ad.le_refl(y)

def aw.le_add_l(f: Nat, -x: Nat, -y: Nat, e: {A.le(x, y) == True{} : Bool}) -> {A.le(Nat.add(f, x), Nat.add(f, y)) == True{} : Bool}:
  match f:
    case 0n:
      e
    case 1n+p:
      aw.le_add_l(p, x, y, e)

def aw.isz_bit(b: Bool, -n: Nat, e: {A.isz(n) == False{} : Bool}) -> {A.isz(A.bit(b, n)) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      {==}

# What w waits for
# ----------------

def aw.pot0(t: List<&2, A.Tk>) -> {A.pot(t, 0n) == A.cnt(A.Holding{}, A.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

# the interactive slots held are part of it
def aw.held_pot(t: List<&2, A.Tk>, +w: Nat) -> {A.le(A.cnt(A.Holding{}, A.Ia{}, t), A.pot(t, w)) == True{} : Bool}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      P.ad.le_refl(A.cnt(A.Holding{}, A.Ia{}, h <> r))
    case +h <> +r 1n+p:
      +hh = A.hit(A.Holding{}, A.Ia{}, h)
      +hw = A.hit(A.Waiting{}, A.Ia{}, h)
      P.ad.le_trans(A.bit(hh, A.cnt(A.Holding{}, A.Ia{}, r)), A.bit(hh, A.pot(r, p)), A.bit(Bool.or(hh, hw), A.pot(r, p)), aw.bit_mono(hh, A.cnt(A.Holding{}, A.Ia{}, r), A.pot(r, p), aw.held_pot(r, p)), aw.bit_or(hh, hw, A.pot(r, p)))

def aw.wait0(h: A.Tk, -r: List<&2, A.Tk>, e: {A.waits.ia(Some{h}) == True{} : Bool}) -> {A.isz(A.cnt(A.Waiting{}, A.Ia{}, h <> r)) == False{} : Bool}:
  match h:
    case A.Tk{A.Ia{}, A.Queued{}}:
      {==}
    case A.Tk{A.Ia{}, A.Granted{}}:
      P.ad.absurd({A.isz(A.cnt(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Granted{}} <> r)) == False{} : Bool}, e)
    case A.Tk{A.Ia{}, A.Held{}}:
      P.ad.absurd({A.isz(A.cnt(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Held{}} <> r)) == False{} : Bool}, e)
    case A.Tk{A.Ia{}, A.Preempted{}}:
      P.ad.absurd({A.isz(A.cnt(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Preempted{}} <> r)) == False{} : Bool}, e)
    case A.Tk{A.Ia{}, A.Ended{}}:
      P.ad.absurd({A.isz(A.cnt(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Ended{}} <> r)) == False{} : Bool}, e)
    case A.Tk{A.Bg{}, s}:
      P.ad.absurd({A.isz(A.cnt(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, s} <> r)) == False{} : Bool}, e)

# an interactive waiter is counted
def aw.wait_cnt(t: List<&2, A.Tk>, w: Nat, e: {A.waits.ia(A.get(t, w)) == True{} : Bool}) -> {A.isz(A.cnt(A.Waiting{}, A.Ia{}, t)) == False{} : Bool}:
  match t w:
    case Nil{} _:
      P.ad.absurd({A.isz(0n) == False{} : Bool}, e)
    case +h <> +r 0n:
      aw.wait0(h, r, e)
    case +h <> +r 1n+p:
      aw.isz_bit(A.hit(A.Waiting{}, A.Ia{}, h), A.cnt(A.Waiting{}, A.Ia{}, r), aw.wait_cnt(r, p, e))

def aw.room_t(l: A.Lim) -> {A.room(l, 0n) == True{} : Bool}:
  match l:
    case A.Unl{}:
      {==}
    case A.Cap{p}:
      {==}

def aw.room00(-l: A.Lim, -hi: Nat, -hb: Nat, zh: {hi == 0n : Nat}, zb: {hb == 0n : Nat}, rf: {A.room(l, Nat.add(hi, hb)) == False{} : Bool}) -> {A.room(l, 0n) == False{} : Bool}:
  %zh : {A.room(l, Nat.add(_, 0n)) == False{} : Bool}
  %zb : {A.room(l, Nat.add(hi, _)) == False{} : Bool}
  rf

# with no interactive slot held, an interactive waiter would have a
# free slot
def aw.no_idle(-X: Type, +l: A.Lim, +hi: Nat, +wi: Nat, +hb: Nat, +wb: Nat, zh: {hi == 0n : Nat}, nz: {A.isz(wi) == False{} : Bool}, +h: {P.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> X:
  match wi:
    case 0n:
      P.ad.absurd_t(X, nz)
    case 1n+w:
      +cn = A.calm.n(hi, 1n+w, hb)
      +zb = P.ad.calm_hb0(hi, w, hb, P.ad.and_r(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(A.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h))
      +rf = P.ad.ok_room(A.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)
      P.ad.absurd_t(X, Equal.trans(Bool, True{}, A.room(l, 0n), False{}, Equal.sym(Bool, A.room(l, 0n), True{}, aw.room_t(l)), aw.room00(l, hi, hb, zh, zb, rf)))

def aw.held_le0(+ts: List<&2, A.Tk>, +w: Nat, ep: {A.pot(ts, w) == 0n : Nat}) -> {A.le(A.cnt(A.Holding{}, A.Ia{}, ts), 0n) == True{} : Bool}:
  %ep : {A.le(A.cnt(A.Holding{}, A.Ia{}, ts), _) == True{} : Bool}
  aw.held_pot(ts, w)

def aw.pos_go(p: Nat, +l: A.Lim, +ts: List<&2, A.Tk>, +w: Nat, ep: {A.pot(ts, w) == p : Nat}, +inv: {P.ad.ok(l, ts) == True{} : Bool}, ws: {A.waits.ia(A.get(ts, w)) == True{} : Bool}) -> {A.le(1n, p) == True{} : Bool}:
  match p:
    case 1n+x:
      {==}
    case 0n:
      +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
      aw.no_idle({A.le(1n, 0n) == True{} : Bool}, l, hi, A.cnt(A.Waiting{}, A.Ia{}, ts), A.cnt(A.Holding{}, A.Bg{}, ts), A.cnt(A.Waiting{}, A.Bg{}, ts), aw.le0(hi, aw.held_le0(ts, w, ep)), aw.wait_cnt(ts, w, ws), inv)

# while w waits, it waits for something
def aw.pot_pos(s: A.St, +w: Nat, inv: {P.ad.okS(s) == True{} : Bool}, ws: {A.waits.ia(A.status(s, w)) == True{} : Bool}) -> {A.le(1n, A.ahead(s, w)) == True{} : Bool}:
  match s:
    case A.St{+l, q, +ts}:
      aw.pos_go(A.pot(ts, w), l, ts, w, {==}, inv, ws)

# What each change does to it
# ---------------------------

def aw.pot_pre(t: List<&2, A.Tk>, +w: Nat) -> {A.pot(A.preempt(t), w) == A.pot(t, w) : Nat}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      P.ad.pre_ia(A.Holding{}, h <> r)
    case +h <> +r 1n+p:
      +hh = A.hit(A.Holding{}, A.Ia{}, h)
      +hw = A.hit(A.Waiting{}, A.Ia{}, h)
      +rhs = A.bit(Bool.or(hh, hw), A.pot(r, p))
      %Equal.sym(Bool, A.hit(A.Holding{}, A.Ia{}, A.Tk.preempt(h)), hh, P.ad.hit_pre(A.Holding{}, h)) : {A.bit(Bool.or(_, A.hit(A.Waiting{}, A.Ia{}, A.Tk.preempt(h))), A.pot(A.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Bool, A.hit(A.Waiting{}, A.Ia{}, A.Tk.preempt(h)), hw, P.ad.hit_pre(A.Waiting{}, h)) : {A.bit(Bool.or(hh, _), A.pot(A.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Nat, A.pot(A.preempt(r), p), A.pot(r, p), aw.pot_pre(r, p)) : {A.bit(Bool.or(hh, hw), _) == rhs : Nat}
      {==}

def aw.wait_pre1(t: A.Tk) -> {A.waits.ia(Some{A.Tk.preempt(t)}) == A.waits.ia(Some{t}) : Bool}:
  match t:
    case A.Tk{A.Ia{}, s}:
      {==}
    case A.Tk{A.Bg{}, A.Queued{}}:
      {==}
    case A.Tk{A.Bg{}, A.Granted{}}:
      {==}
    case A.Tk{A.Bg{}, A.Held{}}:
      {==}
    case A.Tk{A.Bg{}, A.Preempted{}}:
      {==}
    case A.Tk{A.Bg{}, A.Ended{}}:
      {==}

def aw.wait_pre(t: List<&2, A.Tk>, w: Nat) -> {A.waits.ia(A.get(A.preempt(t), w)) == A.waits.ia(A.get(t, w)) : Bool}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      aw.wait_pre1(h)
    case +h <> +r 1n+p:
      aw.wait_pre(r, p)

# a new ticket comes after w
def aw.pot_app(t: List<&2, A.Tk>, +x: A.Tk, +w: Nat, ws: {A.waits.ia(A.get(t, w)) == True{} : Bool}) -> {A.pot(List.append(&2, A.Tk, t, [x]), w) == A.bit(A.hit(A.Holding{}, A.Ia{}, x), A.pot(t, w)) : Nat}:
  match t w:
    case Nil{} _:
      P.ad.absurd({A.pot([x], w) == A.bit(A.hit(A.Holding{}, A.Ia{}, x), 0n) : Nat}, ws)
    case +h <> +r 0n:
      P.ad.cnt_app(A.Holding{}, A.Ia{}, h <> r, x)
    case +h <> +r 1n+p:
      +b = Bool.or(A.hit(A.Holding{}, A.Ia{}, h), A.hit(A.Waiting{}, A.Ia{}, h))
      +hx = A.hit(A.Holding{}, A.Ia{}, x)
      %Equal.sym(Nat, A.pot(List.append(&2, A.Tk, r, [x]), p), A.bit(hx, A.pot(r, p)), aw.pot_app(r, x, p, ws)) : {A.bit(b, _) == A.bit(hx, A.bit(b, A.pot(r, p))) : Nat}
      P.ad.bit_comm(b, hx, A.pot(r, p))

def aw.end0(+r: List<&2, A.Tk>, +q: Nat, -a: Bool, ih: {A.le(A.bit(a, A.pot(A.put(r, q, A.Ended{}), 0n)), A.pot(r, 0n)) == True{} : Bool}) -> {A.le(A.bit(a, A.cnt(A.Holding{}, A.Ia{}, A.put(r, q, A.Ended{}))), A.cnt(A.Holding{}, A.Ia{}, r)) == True{} : Bool}:
  %aw.pot0(A.put(r, q, A.Ended{})) : {A.le(A.bit(a, _), A.cnt(A.Holding{}, A.Ia{}, r)) == True{} : Bool}
  %aw.pot0(r) : {A.le(A.bit(a, A.pot(A.put(r, q, A.Ended{}), 0n)), _) == True{} : Bool}
  ih

# a ticket that ends drops what it weighed (an interactive slot at
# least, if it held one)
def aw.pot_end(t: List<&2, A.Tk>, +k: Nat, +w: Nat) -> {A.le(A.bit(P.ad.at(A.Holding{}, A.Ia{}, A.get(t, k)), A.pot(A.put(t, k, A.Ended{}), w)), A.pot(t, w)) == True{} : Bool}:
  match t k w:
    case Nil{} _ _:
      {==}
    case A.Tk{+c1, +s1} <> +r 0n 0n:
      P.ad.le_refl(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1}), A.cnt(A.Holding{}, A.Ia{}, r)))
    case A.Tk{+c1, +s1} <> +r 0n 1n+p:
      aw.bit_or(A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{c1, s1}), A.pot(r, p))
    case A.Tk{+c1, +s1} <> +r 1n+q 0n:
      +hh = A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1})
      +a = P.ad.at(A.Holding{}, A.Ia{}, A.get(r, q))
      +x = A.cnt(A.Holding{}, A.Ia{}, A.put(r, q, A.Ended{}))
      %P.ad.bit_comm(hh, a, x) : {A.le(_, A.bit(hh, A.cnt(A.Holding{}, A.Ia{}, r))) == True{} : Bool}
      aw.bit_mono(hh, A.bit(a, x), A.cnt(A.Holding{}, A.Ia{}, r), aw.end0(r, q, a, aw.pot_end(r, q, 0n)))
    case A.Tk{+c1, +s1} <> +r 1n+q 1n+p:
      +a = P.ad.at(A.Holding{}, A.Ia{}, A.get(r, q))
      +b = Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{c1, s1}))
      %P.ad.bit_comm(b, a, A.pot(A.put(r, q, A.Ended{}), p)) : {A.le(_, A.bit(b, A.pot(r, p))) == True{} : Bool}
      aw.bit_mono(b, A.bit(a, A.pot(A.put(r, q, A.Ended{}), p)), A.pot(r, p), aw.pot_end(r, q, p))

def aw.c_of(+x: List<&2, A.Tk>, +y: List<&2, A.Tk>, e: {A.pot(x, 0n) == A.pot(y, 0n) : Nat}) -> {A.cnt(A.Holding{}, A.Ia{}, x) == A.cnt(A.Holding{}, A.Ia{}, y) : Nat}:
  %aw.pot0(x) : {_ == A.cnt(A.Holding{}, A.Ia{}, y) : Nat}
  %aw.pot0(y) : {A.pot(x, 0n) == _ : Nat}
  e

def aw.col0(+c1: A.Cls, s1: A.Sts, -r: List<&2, A.Tk>, w: Nat, g: {P.ad.isg(Some{A.Tk{c1, s1}}) == True{} : Bool}) -> {A.pot(A.Tk{c1, A.Held{}} <> r, w) == A.pot(A.Tk{c1, s1} <> r, w) : Nat}:
  match s1:
    case A.Granted{}:
      match w:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case A.Queued{}:
      P.ad.absurd({A.pot(A.Tk{c1, A.Held{}} <> r, w) == A.pot(A.Tk{c1, A.Queued{}} <> r, w) : Nat}, g)
    case A.Held{}:
      P.ad.absurd({A.pot(A.Tk{c1, A.Held{}} <> r, w) == A.pot(A.Tk{c1, A.Held{}} <> r, w) : Nat}, g)
    case A.Preempted{}:
      P.ad.absurd({A.pot(A.Tk{c1, A.Held{}} <> r, w) == A.pot(A.Tk{c1, A.Preempted{}} <> r, w) : Nat}, g)
    case A.Ended{}:
      P.ad.absurd({A.pot(A.Tk{c1, A.Held{}} <> r, w) == A.pot(A.Tk{c1, A.Ended{}} <> r, w) : Nat}, g)

# collecting a grant changes nothing w waits for
def aw.pot_col(t: List<&2, A.Tk>, +k: Nat, +w: Nat, +g: {P.ad.isg(A.get(t, k)) == True{} : Bool}) -> {A.pot(A.put(t, k, A.Held{}), w) == A.pot(t, w) : Nat}:
  match t k w:
    case Nil{} _ _:
      {==}
    case A.Tk{+c1, +s1} <> +r 0n 0n:
      aw.col0(c1, s1, r, 0n, g)
    case A.Tk{+c1, +s1} <> +r 0n 1n+p:
      aw.col0(c1, s1, r, 1n+p, g)
    case A.Tk{+c1, +s1} <> +r 1n+q 0n:
      +hh = A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1})
      Equal.cong(Nat, Nat, y => A.bit(hh, y), A.cnt(A.Holding{}, A.Ia{}, A.put(r, q, A.Held{})), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.put(r, q, A.Held{}), r, aw.pot_col(r, q, 0n, g)))
    case A.Tk{+c1, +s1} <> +r 1n+q 1n+p:
      +b = Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{c1, s1}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{c1, s1}))
      Equal.cong(Nat, Nat, y => A.bit(b, y), A.pot(A.put(r, q, A.Held{}), p), A.pot(r, p), aw.pot_col(r, q, p, g))

# a grant never makes a ticket wait
def aw.wait_mark(t: List<&2, A.Tk>, +c: A.Cls, +w: Nat, e: {A.waits.ia(A.get(A.mark(c, t), w)) == True{} : Bool}) -> {A.waits.ia(A.get(t, w)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Ia{} A.Queued{}:
          match c w:
            case A.Ia{} 0n:
              P.ad.absurd({A.waits.ia(Some{A.Tk{A.Ia{}, A.Queued{}}}) == True{} : Bool}, e)
            case A.Ia{} 1n+p:
              e
            case A.Bg{} 0n:
              {==}
            case A.Bg{} 1n+p:
              aw.wait_mark(r, A.Bg{}, p, e)
        case A.Bg{} A.Queued{}:
          match c w:
            case A.Bg{} 0n:
              P.ad.absurd({A.waits.ia(Some{A.Tk{A.Bg{}, A.Queued{}}}) == True{} : Bool}, e)
            case A.Bg{} 1n+p:
              e
            case A.Ia{} 0n:
              e
            case A.Ia{} 1n+p:
              aw.wait_mark(r, A.Ia{}, p, e)
        case _ A.Granted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ A.Held{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ A.Preempted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ A.Ended{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)

def aw.wait_grant(+n: Nat, +d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +w: Nat, e: {A.waits.ia(A.get(A.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {A.waits.ia(A.get(t, w)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      aw.wait_mark(t, c, w, aw.wait_grant(f, A.pick(l, A.mark(c, t)), l, A.mark(c, t), w, e))

# an interactive grant while w waits goes to a waiter ahead of it: it
# moves from waiting to holding, which w waits for alike
def aw.pot_mark_ia(t: List<&2, A.Tk>, +w: Nat, +e: {A.waits.ia(A.get(A.mark(A.Ia{}, t), w)) == True{} : Bool}) -> {A.pot(A.mark(A.Ia{}, t), w) == A.pot(t, w) : Nat}:
  match t:
    case Nil{}:
      {==}
    case A.Tk{+hc, +hs} <> +r:
      match hc hs w:
        case A.Ia{} A.Queued{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Ia{}, A.Granted{}} <> r, 0n) == A.pot(A.Tk{A.Ia{}, A.Queued{}} <> r, 0n) : Nat}, e)
        case A.Ia{} A.Queued{} 1n+p:
          {==}
        case A.Ia{} A.Granted{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Ia{}, A.Granted{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Ia{}, A.Granted{}} <> r, 0n) : Nat}, e)
        case A.Ia{} A.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Granted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Granted{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Ia{} A.Held{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Ia{}, A.Held{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Ia{}, A.Held{}} <> r, 0n) : Nat}, e)
        case A.Ia{} A.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Held{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Held{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Ia{} A.Preempted{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Ia{}, A.Preempted{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Ia{}, A.Preempted{}} <> r, 0n) : Nat}, e)
        case A.Ia{} A.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Preempted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Preempted{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Ia{} A.Ended{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Ia{}, A.Ended{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Ia{}, A.Ended{}} <> r, 0n) : Nat}, e)
        case A.Ia{} A.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Ended{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Ended{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Bg{} A.Queued{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Bg{}, A.Queued{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Bg{}, A.Queued{}} <> r, 0n) : Nat}, e)
        case A.Bg{} A.Queued{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Bg{}, A.Queued{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, A.Queued{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Bg{} A.Granted{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Bg{}, A.Granted{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Bg{}, A.Granted{}} <> r, 0n) : Nat}, e)
        case A.Bg{} A.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Bg{}, A.Granted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, A.Granted{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Bg{} A.Held{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Bg{}, A.Held{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Bg{}, A.Held{}} <> r, 0n) : Nat}, e)
        case A.Bg{} A.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Bg{}, A.Held{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, A.Held{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Bg{} A.Preempted{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Bg{}, A.Preempted{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Bg{}, A.Preempted{}} <> r, 0n) : Nat}, e)
        case A.Bg{} A.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Bg{}, A.Preempted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, A.Preempted{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))
        case A.Bg{} A.Ended{} 0n:
          P.ad.absurd({A.pot(A.Tk{A.Bg{}, A.Ended{}} <> A.mark(A.Ia{}, r), 0n) == A.pot(A.Tk{A.Bg{}, A.Ended{}} <> r, 0n) : Nat}, e)
        case A.Bg{} A.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Bg{}, A.Ended{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Bg{}, A.Ended{}})), y), A.pot(A.mark(A.Ia{}, r), p), A.pot(r, p), aw.pot_mark_ia(r, p, e))

# a background grant changes nothing w waits for
def aw.pot_mark_bg(t: List<&2, A.Tk>, +w: Nat) -> {A.pot(A.mark(A.Bg{}, t), w) == A.pot(t, w) : Nat}:
  match t:
    case Nil{}:
      {==}
    case A.Tk{+hc, +hs} <> +r:
      match hc hs w:
        case A.Bg{} A.Queued{} 0n:
          {==}
        case A.Bg{} A.Queued{} 1n+p:
          {==}
        case A.Ia{} A.Queued{} 0n:
          Equal.cong(Nat, Nat, y => A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Queued{}}), y), A.cnt(A.Holding{}, A.Ia{}, A.mark(A.Bg{}, r)), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.mark(A.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case A.Ia{} A.Queued{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.Queued{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Queued{}})), y), A.pot(A.mark(A.Bg{}, r), p), A.pot(r, p), aw.pot_mark_bg(r, p))
        case _ A.Granted{} 0n:
          Equal.cong(Nat, Nat, y => A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Granted{}}), y), A.cnt(A.Holding{}, A.Ia{}, A.mark(A.Bg{}, r)), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.mark(A.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ A.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Granted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Granted{}})), y), A.pot(A.mark(A.Bg{}, r), p), A.pot(r, p), aw.pot_mark_bg(r, p))
        case _ A.Held{} 0n:
          Equal.cong(Nat, Nat, y => A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Held{}}), y), A.cnt(A.Holding{}, A.Ia{}, A.mark(A.Bg{}, r)), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.mark(A.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ A.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Held{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Held{}})), y), A.pot(A.mark(A.Bg{}, r), p), A.pot(r, p), aw.pot_mark_bg(r, p))
        case _ A.Preempted{} 0n:
          Equal.cong(Nat, Nat, y => A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Preempted{}}), y), A.cnt(A.Holding{}, A.Ia{}, A.mark(A.Bg{}, r)), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.mark(A.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ A.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Preempted{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Preempted{}})), y), A.pot(A.mark(A.Bg{}, r), p), A.pot(r, p), aw.pot_mark_bg(r, p))
        case _ A.Ended{} 0n:
          Equal.cong(Nat, Nat, y => A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Ended{}}), y), A.cnt(A.Holding{}, A.Ia{}, A.mark(A.Bg{}, r)), A.cnt(A.Holding{}, A.Ia{}, r), aw.c_of(A.mark(A.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ A.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => A.bit(Bool.or(A.hit(A.Holding{}, A.Ia{}, A.Tk{hc, A.Ended{}}), A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Ended{}})), y), A.pot(A.mark(A.Bg{}, r), p), A.pot(r, p), aw.pot_mark_bg(r, p))

def aw.pot_grant(+n: Nat, +d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +w: Nat, +e: {A.waits.ia(A.get(A.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {A.pot(A.grant.go(n, d, l, t), w) == A.pot(t, w) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{A.Ia{}}:
      +t2 = A.mark(A.Ia{}, t)
      Equal.trans(Nat, A.pot(A.grant.go(f, A.pick(l, t2), l, t2), w), A.pot(t2, w), A.pot(t, w), aw.pot_grant(f, A.pick(l, t2), l, t2, w, e), aw.pot_mark_ia(t, w, aw.wait_grant(f, A.pick(l, t2), l, t2, w, e)))
    case 1n+f Some{A.Bg{}}:
      +t2 = A.mark(A.Bg{}, t)
      Equal.trans(Nat, A.pot(A.grant.go(f, A.pick(l, t2), l, t2), w), A.pot(t2, w), A.pot(t, w), aw.pot_grant(f, A.pick(l, t2), l, t2, w, e), aw.pot_mark_bg(t, w))

# One op
# ------

def aw.ia_new(-r: Bool, u: Bool, +p: Nat) -> {A.le(A.bit(Bool.and(A.Mode.of(A.Holding{}, A.admit.ia.st(Bool.and(False{}, r), u)), True{}), p), p) == True{} : Bool}:
  match u:
    case True{}:
      P.ad.le_refl(p)
    case False{}:
      P.ad.le_refl(p)

# a new interactive request waits behind w
def aw.st_ia(+l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +w: Nat, +ws: {A.waits.ia(A.get(ts, w)) == True{} : Bool}) -> {A.le(A.pot(A.admit.ia(l, q, ts), w), A.pot(ts, w)) == True{} : Bool}:
  +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
  +st = A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))
  +x = {A.Tk{A.Ia{}, st} : A.Tk}
  +t1 = A.preempt(ts)
  +p = A.pot(ts, w)
  +ws1 = Equal.trans(Bool, A.waits.ia(A.get(t1, w)), A.waits.ia(A.get(ts, w)), True{}, aw.wait_pre(ts, w), ws)
  %Equal.sym(Nat, A.pot(List.append(&2, A.Tk, t1, [x]), w), A.bit(A.hit(A.Holding{}, A.Ia{}, x), A.pot(t1, w)), aw.pot_app(t1, x, w, ws1)) : {A.le(_, p) == True{} : Bool}
  %Equal.sym(Nat, A.pot(t1, w), p, aw.pot_pre(ts, w)) : {A.le(A.bit(A.hit(A.Holding{}, A.Ia{}, x), _), p) == True{} : Bool}
  %Equal.sym(Bool, A.isz(wi), False{}, aw.wait_cnt(ts, w, ws)) : {A.le(A.bit(Bool.and(A.Mode.of(A.Holding{}, A.admit.ia.st(Bool.and(_, A.room(l, hi)), A.le(q, wi))), True{}), p), p) == True{} : Bool}
  aw.ia_new(A.room(l, hi), A.le(q, wi), p)

# a new background request changes nothing w waits for
def aw.st_bg(+l: A.Lim, +ts: List<&2, A.Tk>, +w: Nat, ws: {A.waits.ia(A.get(ts, w)) == True{} : Bool}) -> {A.le(A.pot(A.admit.bg(l, ts), w), A.pot(ts, w)) == True{} : Bool}:
  +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
  +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, ts)
  +st = A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))
  +y = {A.Tk{A.Bg{}, st} : A.Tk}
  +p = A.pot(ts, w)
  %Equal.sym(Nat, A.pot(List.append(&2, A.Tk, ts, [y]), w), A.bit(A.hit(A.Holding{}, A.Ia{}, y), p), aw.pot_app(ts, y, w, ws)) : {A.le(_, p) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(A.Mode.of(A.Holding{}, st), False{}), False{}, P.ad.and_f(A.Mode.of(A.Holding{}, st))) : {A.le(A.bit(_, p), p) == True{} : Bool}
  P.ad.le_refl(p)

def aw.end_at(+ts: List<&2, A.Tk>, +k: Nat, +w: Nat, -mb: Maybe<&2, A.Tk>, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {A.le(A.bit(P.ad.at(A.Holding{}, A.Ia{}, mb), A.pot(A.put(ts, k, A.Ended{}), w)), A.pot(ts, w)) == True{} : Bool}:
  %ej : {A.le(A.bit(P.ad.at(A.Holding{}, A.Ia{}, _), A.pot(A.put(ts, k, A.Ended{}), w)), A.pot(ts, w)) == True{} : Bool}
  aw.pot_end(ts, k, w)

def aw.col(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +w: Nat, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {A.le(A.pot(A.St.ts(A.collect.at(mb, l, q, ts, k)), w), A.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{c, A.Queued{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{+c, A.Granted{}}}:
      %Equal.sym(Nat, A.pot(A.put(ts, k, A.Held{}), w), A.pot(ts, w), aw.pot_col(ts, k, w, P.ad.isg_at(ts, k, Some{A.Tk{c, A.Granted{}}}, ej, {==}))) : {A.le(_, A.pot(ts, w)) == True{} : Bool}
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{c, A.Held{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{c, A.Preempted{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{c, A.Ended{}}}:
      P.ad.le_refl(A.pot(ts, w))

def aw.rel(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +w: Nat, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, wf: {A.waits.ia(A.get(A.St.ts(A.release.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {A.le(Nat.add(A.frees.at(mb, True{}), A.pot(A.St.ts(A.release.at(mb, l, q, ts, k)), w)), A.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Queued{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Granted{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Held{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Ia{}, A.Held{}}}, True{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Ia{}, A.Held{}}}, ej)
    case Some{A.Tk{A.Ia{}, A.Preempted{}}}:
      aw.end_at(ts, k, w, Some{A.Tk{A.Ia{}, A.Preempted{}}}, ej)
    case Some{A.Tk{A.Ia{}, A.Ended{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Queued{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Granted{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Held{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Bg{}, A.Held{}}}, True{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Bg{}, A.Held{}}}, ej)
    case Some{A.Tk{A.Bg{}, A.Preempted{}}}:
      aw.end_at(ts, k, w, Some{A.Tk{A.Bg{}, A.Preempted{}}}, ej)
    case Some{A.Tk{A.Bg{}, A.Ended{}}}:
      P.ad.le_refl(A.pot(ts, w))

def aw.lea(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +w: Nat, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, wf: {A.waits.ia(A.get(A.St.ts(A.leave.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {A.le(Nat.add(A.frees.at(mb, False{}), A.pot(A.St.ts(A.leave.at(mb, l, q, ts, k)), w)), A.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Queued{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Ia{}, A.Queued{}}}, False{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Ia{}, A.Queued{}}}, ej)
    case Some{A.Tk{A.Ia{}, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Ia{}, A.Granted{}}}, False{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Ia{}, A.Granted{}}}, ej)
    case Some{A.Tk{A.Ia{}, A.Held{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Preempted{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Ia{}, A.Ended{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Queued{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Bg{}, A.Queued{}}}, False{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Bg{}, A.Queued{}}}, ej)
    case Some{A.Tk{A.Bg{}, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.pot(A.grant(l, t2), w), A.pot(t2, w), aw.pot_grant(A.waits(t2), A.pick(l, t2), l, t2, w, wf)) : {A.le(Nat.add(A.frees.at(Some{A.Tk{A.Bg{}, A.Granted{}}}, False{}), _), A.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{A.Tk{A.Bg{}, A.Granted{}}}, ej)
    case Some{A.Tk{A.Bg{}, A.Held{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Preempted{}}}:
      P.ad.le_refl(A.pot(ts, w))
    case Some{A.Tk{A.Bg{}, A.Ended{}}}:
      P.ad.le_refl(A.pot(ts, w))

def aw.step(s: A.St, o: A.Op, +w: Nat, +ws: {A.waits.ia(A.status(s, w)) == True{} : Bool}, wf: {A.waits.ia(A.status(A.step(s, o), w)) == True{} : Bool}) -> {A.le(Nat.add(A.frees(s, o), A.ahead(A.step(s, o), w)), A.ahead(s, w)) == True{} : Bool}:
  match s o:
    case A.St{+l, +q, +ts} A.Admit{A.Ia{}}:
      aw.st_ia(l, q, ts, w, ws)
    case A.St{+l, +q, +ts} A.Admit{A.Bg{}}:
      aw.st_bg(l, ts, w, ws)
    case A.St{+l, +q, +ts} A.Collect{+k}:
      aw.col(A.get(ts, k), l, q, ts, k, w, {==})
    case A.St{+l, +q, +ts} A.Release{+k}:
      aw.rel(A.get(ts, k), l, q, ts, k, w, {==}, wf)
    case A.St{+l, +q, +ts} A.Leave{+k}:
      aw.lea(A.get(ts, k), l, q, ts, k, w, {==}, wf)
    case A.St{+l, +q, +ts} A.Limit{+l2, q2}:
      %Equal.sym(Nat, A.pot(A.grant(l2, ts), w), A.pot(ts, w), aw.pot_grant(A.waits(ts), A.pick(l2, ts), l2, ts, w, wf)) : {A.le(_, A.pot(ts, w)) == True{} : Bool}
      P.ad.le_refl(A.pot(ts, w))

# A run
# -----

def aw.thru_head(os: List<&2, A.Op>, +s: A.St, +w: Nat, e: {A.waits.thru(os, s, w) == True{} : Bool}) -> {A.waits.ia(A.status(s, w)) == True{} : Bool}:
  match os:
    case Nil{}:
      e
    case +o <> r:
      P.ad.and_l(A.waits.ia(A.status(s, w)), A.waits.thru(r, A.step(s, o), w), e)

def aw.trace(os: List<&2, A.Op>, +s: A.St, +w: Nat, +inv: {P.ad.okS(s) == True{} : Bool}, +e: {A.waits.thru(os, s, w) == True{} : Bool}) -> {A.le(1n+A.frees.run(os, s), A.ahead(s, w)) == True{} : Bool}:
  match os:
    case Nil{}:
      aw.pot_pos(s, w, inv, e)
    case +o <> +r:
      +s2 = A.step(s, o)
      +f = A.frees(s, o)
      +ff = A.frees.run(r, s2)
      +a1 = A.ahead(s2, w)
      +a0 = A.ahead(s, w)
      +e2 = P.ad.and_r(A.waits.ia(A.status(s, w)), A.waits.thru(r, s2, w), e)
      +ih = aw.trace(r, s2, w, P.ad.step_ok(s, o, inv), e2)
      +st = aw.step(s, o, w, P.ad.and_l(A.waits.ia(A.status(s, w)), A.waits.thru(r, s2, w), e), aw.thru_head(r, s2, w, e2))
      %Equal.sym(Nat, 1n+Nat.add(f, ff), Nat.add(f, 1n+ff), P.ad.add_succ(f, ff)) : {A.le(_, a0) == True{} : Bool}
      P.ad.le_trans(Nat.add(f, 1n+ff), Nat.add(f, a1), a0, aw.le_add_l(f, 1n+ff, a1, ih), st)

# Laws (e)
# --------

def interactive_step(s: A.St, o: A.Op, +w: Nat, ws: {A.waits.ia(A.status(s, w)) == True{} : Bool}, wf: {A.waits.ia(A.status(A.step(s, o), w)) == True{} : Bool}) -> {A.le(Nat.add(A.frees(s, o), A.ahead(A.step(s, o), w)), A.ahead(s, w)) == True{} : Bool}:
  aw.step(s, o, w, ws, wf)

def interactive_bound(+l: A.Lim, +q: Nat, +pre: List<&2, A.Op>, +os: List<&2, A.Op>, +w: Nat, e: {A.waits.thru(os, A.run(pre, A.St.new(l, q)), w) == True{} : Bool}) -> {A.le(1n+A.frees.run(os, A.run(pre, A.St.new(l, q))), A.ahead(A.run(pre, A.St.new(l, q)), w)) == True{} : Bool}:
  aw.trace(os, A.run(pre, A.St.new(l, q)), w, P.ad.run_ok(pre, A.St.new(l, q), P.ad.new_ok(l, q)), e)
