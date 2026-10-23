# eukhe: lemmas the proofs of area admission share: admission/misc

import Base
import ../../../../bend/admission.bend as Ad
import ../bool.bend as LABool

# A preemption
# ------------

# it keeps an interactive ticket's counts
def ad.hit_pre(+m: Ad.Mode, t: Ad.Tk) -> {Ad.hit(m, Ad.Ia{}, Ad.Tk.preempt(t)) == Ad.hit(m, Ad.Ia{}, t) : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      {==}
    case Ad.Tk{Ad.Bg{}, s}:
      match s:
        case Ad.Queued{}:
          {==}
        case Ad.Granted{}:
          LABool.ad.and_ff(Ad.Mode.of(m, Ad.Queued{}), Ad.Mode.of(m, Ad.Granted{}))
        case Ad.Held{}:
          LABool.ad.and_ff(Ad.Mode.of(m, Ad.Preempted{}), Ad.Mode.of(m, Ad.Held{}))
        case Ad.Preempted{}:
          {==}
        case Ad.Ended{}:
          {==}

def ad.pre_ia(+m: Ad.Mode, t: List<&2, Ad.Tk>) -> {Ad.cnt(m, Ad.Ia{}, Ad.preempt(t)) == Ad.cnt(m, Ad.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, Ad.hit(m, Ad.Ia{}, Ad.Tk.preempt(h)), Ad.hit(m, Ad.Ia{}, h), ad.hit_pre(m, h)) : {Ad.bit(_, Ad.cnt(m, Ad.Ia{}, Ad.preempt(r))) == Ad.bit(Ad.hit(m, Ad.Ia{}, h), Ad.cnt(m, Ad.Ia{}, r)) : Nat}
      %Equal.sym(Nat, Ad.cnt(m, Ad.Ia{}, Ad.preempt(r)), Ad.cnt(m, Ad.Ia{}, r), ad.pre_ia(m, r)) : {Ad.bit(Ad.hit(m, Ad.Ia{}, h), _) == Ad.bit(Ad.hit(m, Ad.Ia{}, h), Ad.cnt(m, Ad.Ia{}, r)) : Nat}
      {==}

# it leaves no background slot held
def ad.hb_pre(t: Ad.Tk) -> {Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk.preempt(t)) == False{} : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, s))
    case Ad.Tk{Ad.Bg{}, s}:
      match s:
        case Ad.Queued{}:
          {==}
        case Ad.Granted{}:
          {==}
        case Ad.Held{}:
          {==}
        case Ad.Preempted{}:
          {==}
        case Ad.Ended{}:
          {==}

def ad.pre_hb(t: List<&2, Ad.Tk>) -> {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.preempt(t)) == 0n : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk.preempt(h)), False{}, ad.hb_pre(h)) : {Ad.bit(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.preempt(r))) == 0n : Nat}
      ad.pre_hb(r)

def ad.m_ia(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}, u: LABool.ad.BD(LABool.ad.mis(m, Ad.Ia{}), X, Unit)) -> X:
  %e : LABool.ad.BD(LABool.ad.mis(_, Ad.Ia{}), X, Unit)
  u

def ad.m_bg(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}, u: LABool.ad.BD(LABool.ad.mis(m, Ad.Bg{}), X, Unit)) -> X:
  %e : LABool.ad.BD(LABool.ad.mis(_, Ad.Bg{}), X, Unit)
  u

def ad.pick_none0(r: Bool, hi: Nat) -> {Ad.pick.go(r, 0n, hi, 0n) == None{} : Maybe<&2, Ad.Cls>}:
  match r hi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+x:
      {==}

def ad.pick_none_hi(r: Bool, -hi: Nat, -wb: Nat) -> {Ad.pick.go(r, 0n, 1n+hi, wb) == None{} : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# with interactive slots held, background waiters do not matter
def ad.pick_hi(r: Bool, wi: Nat, -a: Nat, -x: Nat, -y: Nat) -> {Ad.pick.go(r, wi, 1n+a, x) == Ad.pick.go(r, wi, 1n+a, y) : Maybe<&2, Ad.Cls>}:
  match r wi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+b:
      {==}

# with interactive waiters, background waiters do not matter
def ad.pick_wi(r: Bool, -b: Nat, -h: Nat, -x: Nat, -y: Nat) -> {Ad.pick.go(r, 1n+b, h, x) == Ad.pick.go(r, 1n+b, h, y) : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

def ad.pick_wb(r: Bool, -x: Nat, -y: Nat) -> {Ad.pick.go(r, 0n, 0n, 1n+x) == Ad.pick.go(r, 0n, 0n, 1n+y) : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# a grant to an interactive waiter: one waits
def ad.pick_ia(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}) -> {Ad.isz(wi) == False{} : Bool}:
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_ia({Ad.isz(wi) == False{} : Bool}, None{}, e, Unit{})
    case True{} 1n+a _ _:
      {==}
    case True{} 0n 1n+b _:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, Some{Ad.Bg{}}, e, Unit{})

# a grant to a background waiter: no interactive request holds or waits,
# and one background request waits
def ad.pick_bg(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}):
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_bg({wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 1n+a _ _:
      ad.m_bg({1n+a == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), Some{Ad.Ia{}}, e, Unit{})
    case True{} 0n 1n+b _:
      ad.m_bg({0n == 0n : Nat} & ({1n+b == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_bg({0n == 0n : Nat} & ({0n == 0n : Nat} & {Ad.isz(0n) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ({==}, ({==}, {==}))

def ad.grant_none(+l: Ad.Lim, +t: List<&2, Ad.Tk>, ed: {Ad.pick(l, t) == None{} : Maybe<&2, Ad.Cls>}, cm: {Ad.calm(t) == True{} : Bool}) -> {LABool.ad.ok(l, t) == True{} : Bool}:
  +p = Ad.pick(l, t)
  LABool.ad.and_t(Bool.not(Maybe.is_some(&2, Ad.Cls, p)), Ad.calm(t), LABool.ad.not_none(p, ed), cm)

def ad.pbg(+l: Ad.Lim, +t: List<&2, Ad.Tk>, e: {Ad.pick(l, t) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}):
  ad.pick_bg(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), e)

def ad.bg_wi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  a

def ad.bg_hi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  b

def ad.bg_wb(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}:
  (a, b, c) = p
  c

def ad.new_ok(l: Ad.Lim, -q: Nat) -> {LABool.ad.okS(Ad.St.new(l, q)) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def ad.end_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.mark(c, t), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c k:
            case Ad.Ia{} 0n:
              LABool.ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Ia{} 1n+p:
              e
            case Ad.Bg{} 0n:
              e
            case Ad.Bg{} 1n+p:
              ad.end_mark(r, Ad.Bg{}, p, e)
        case Ad.Bg{} Ad.Queued{}:
          match c k:
            case Ad.Bg{} 0n:
              LABool.ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Bg{} 1n+p:
              e
            case Ad.Ia{} 0n:
              e
            case Ad.Ia{} 1n+p:
              ad.end_mark(r, Ad.Ia{}, p, e)
        case _ Ad.Granted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Held{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Preempted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Ended{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)

def ad.end_grant_k(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.grant.go(n, d, l, t), k)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      ad.end_grant_k(f, Ad.pick(l, Ad.mark(c, t)), l, Ad.mark(c, t), k, ad.end_mark(t, c, k, e))

def ad.isg_at(-ts: List<&2, Ad.Tk>, -k: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, f: {LABool.ad.isg(mb) == True{} : Bool}) -> {LABool.ad.isg(Ad.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), mb, ej) : {LABool.ad.isg(_) == True{} : Bool}
  f

def aw.isz_bit(b: Bool, -n: Nat, e: {Ad.isz(n) == False{} : Bool}) -> {Ad.isz(Ad.bit(b, n)) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      {==}

def aw.wait0(h: Ad.Tk, -r: List<&2, Ad.Tk>, e: {Ad.waits.ia(Some{h}) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, h <> r)) == False{} : Bool}:
  match h:
    case Ad.Tk{Ad.Ia{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Ia{}, Ad.Granted{}}:
      LABool.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Held{}}:
      LABool.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Preempted{}}:
      LABool.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Ended{}}:
      LABool.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Bg{}, s}:
      LABool.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, s} <> r)) == False{} : Bool}, e)

# an interactive waiter is counted
def aw.wait_cnt(t: List<&2, Ad.Tk>, w: Nat, e: {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}:
  match t w:
    case Nil{} _:
      LABool.ad.absurd({Ad.isz(0n) == False{} : Bool}, e)
    case +h <> +r 0n:
      aw.wait0(h, r, e)
    case +h <> +r 1n+p:
      aw.isz_bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, h), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, r), aw.wait_cnt(r, p, e))
