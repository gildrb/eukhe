# eukhe: lemmas the proofs of area admission share: admission/lv

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission
import ../list.bend as LAList
import ../logic.bend as LALogic
import ../nat.bend as LANat

# Counting
# --------

def al.keep_cnt(s: Ad.Sts, +m: Ad.Mode, +c: Ad.Cls, +j: Nat, +c2: Ad.Cls, +rest: List<&2, Ad.Lv>) -> {Ad.lv.cnt(m, c, Admission.adl_keep(s, j, c2, rest)) == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.lv.cnt(m, c, rest)) : Nat}:
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
      match m:
        case Ad.Holding{}:
          {==}
        case Ad.Waiting{}:
          {==}

def al.cnt(+m: Ad.Mode, +c: Ad.Cls, ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)) == Ad.cnt(m, c, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c2, +s} <> +r:
      %Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_keep(s, j, c2, Admission.adl_lives(r, 1n+j))), Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.lv.cnt(m, c, Admission.adl_lives(r, 1n+j))), al.keep_cnt(s, m, c, j, c2, Admission.adl_lives(r, 1n+j))) : {_ == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.cnt(m, c, r)) : Nat}
      %Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_lives(r, 1n+j)), Ad.cnt(m, c, r), al.cnt(m, c, r, 1n+j)) : {Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), _) == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.cnt(m, c, r)) : Nat}
      {==}

# a count of the live tickets is the count of the model's tickets
def al.cnt_s(+m: Ad.Mode, +c: Ad.Cls, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.cnt(m, c, ts) == Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)) : Nat}:
  Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)), Ad.cnt(m, c, ts), al.cnt(m, c, ts, j))

def al.held(+ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.held(Admission.adl_lives(ts, j)) == Ad.held(ts) : Nat}:
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, j) : {Nat.add(_, Ad.lv.cnt(Ad.Holding{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.held(ts) : Nat}
  %al.cnt_s(Ad.Holding{}, Ad.Bg{}, ts, j) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == Ad.held(ts) : Nat}
  {==}

def al.waits(+ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.waits(Admission.adl_lives(ts, j)) == Ad.waits(ts) : Nat}:
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, j) : {Nat.add(_, Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.waits(ts) : Nat}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, j) : {Nat.add(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), _) == Ad.waits(ts) : Nat}
  {==}

def al.pick(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.pick(l, Admission.adl_lives(ts, j)) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}:
  %Equal.sym(Nat, Ad.lv.held(Admission.adl_lives(ts, j)), Ad.held(ts), al.held(ts, j)) : {Ad.pick.go(Ad.room(l, _), Ad.lv.cnt(Ad.Waiting{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), _, Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), _, Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  {==}

# Granting
# --------

def al.mark_at(b: Bool, +c: Ad.Cls, +j: Nat, +c2: Ad.Cls, s: Ad.Sts, +r: List<&2, Ad.Tk>, ne: {Ad.ended(Some{Ad.Tk{c2, s}}) == False{} : Bool}, ih: {Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)) == Admission.adl_lives(Ad.mark(c, r), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.mark.at(b, c, Ad.Lv{j, c2, s}, Admission.adl_lives(r, 1n+j), Ad.lv.mark(c, Admission.adl_lives(r, 1n+j))) == Admission.adl_lives(Ad.mark.at(b, c, Ad.Tk{c2, s}, r, Ad.mark(c, r)), j) : List<&2, Ad.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match s:
        case Ad.Queued{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Queued{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Granted{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Granted{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Held{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Held{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Preempted{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Preempted{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Ended{}:
          LALogic.al.absurd({Ad.lv.mark.at(False{}, c, Ad.Lv{j, c2, Ad.Ended{}}, Admission.adl_lives(r, 1n+j), Ad.lv.mark(c, Admission.adl_lives(r, 1n+j))) == Admission.adl_lives(Ad.mark.at(False{}, c, Ad.Tk{c2, Ad.Ended{}}, r, Ad.mark(c, r)), j) : List<&2, Ad.Lv>}, ne)

def al.mark(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.mark(c, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.mark(c, ts), j) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c2, s} <> +r:
      match s:
        case Ad.Queued{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Queued{}}), c, j, c2, Ad.Queued{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Granted{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Granted{}}), c, j, c2, Ad.Granted{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Held{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Held{}}), c, j, c2, Ad.Held{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Preempted{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Preempted{}}), c, j, c2, Ad.Preempted{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Ended{}:
          al.mark(c, r, 1n+j)

def al.grant_go(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.grant.go(n, d, l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant.go(n, d, l, ts), j) : List<&2, Ad.Lv>}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{+c}:
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.mark(c, Admission.adl_lives(ts, j)), Admission.adl_lives(Ad.mark(c, ts), j), al.mark(c, ts, j)) : {Ad.lv.grant.go(f, Ad.lv.pick(l, _), l, _) == Admission.adl_lives(Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), j) : List<&2, Ad.Lv>}
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.lv.pick(l, Admission.adl_lives(Ad.mark(c, ts), j)), Ad.pick(l, Ad.mark(c, ts)), al.pick(l, Ad.mark(c, ts), j)) : {Ad.lv.grant.go(f, _, l, Admission.adl_lives(Ad.mark(c, ts), j)) == Admission.adl_lives(Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), j) : List<&2, Ad.Lv>}
      al.grant_go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts), j)

def al.grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.grant(l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}:
  %Equal.sym(Nat, Ad.lv.waits(Admission.adl_lives(ts, j)), Ad.waits(ts), al.waits(ts, j)) : {Ad.lv.grant.go(_, Ad.lv.pick(l, Admission.adl_lives(ts, j)), l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}
  %Equal.sym(Maybe<&2, Ad.Cls>, Ad.lv.pick(l, Admission.adl_lives(ts, j)), Ad.pick(l, ts), al.pick(l, ts, j)) : {Ad.lv.grant.go(Ad.waits(ts), _, l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}
  al.grant_go(Ad.waits(ts), Ad.pick(l, ts), l, ts, j)

# Preempting
# ----------

def al.preempt(ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.preempt(Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.preempt(ts), j) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> +r:
      match c:
        case Ad.Ia{}:
          match s:
            case Ad.Queued{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Granted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Granted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Held{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Held{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Preempted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Ended{}:
              al.preempt(r, 1n+j)
        case Ad.Bg{}:
          match s:
            case Ad.Queued{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Granted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Held{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Preempted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Ended{}:
              al.preempt(r, 1n+j)

# Admitting
# ---------

def al.fresh(s: Ad.Sts, +k: Nat, +c: Ad.Cls) -> {Admission.adl_keep(s, k, c, Nil{}) == Ad.lv.fresh(s, k, c) : List<&2, Ad.Lv>}:
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

# a ticket appended to the model's tickets is the live ticket appended
def al.app(a: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Ad.Sts, +j: Nat) -> {Admission.adl_lives(List.append(&2, Ad.Tk, a, [Ad.Tk{c, s}]), j) == List.append(&2, Ad.Lv, Admission.adl_lives(a, j), Ad.lv.fresh(s, Nat.add(List.length(&2, Ad.Tk, a), j), c)) : List<&2, Ad.Lv>}:
  match a:
    case Nil{}:
      al.fresh(s, j, c)
    case Ad.Tk{+c2, +s2} <> +r:
      +x = {Ad.Tk{c, s} : Ad.Tk}
      +n = {List.length(&2, Ad.Tk, r) : Nat}
      %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, r, [x]), 1n+j), List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, Nat.add(n, 1n+j), c)), al.app(r, c, s, 1n+j)) : {Admission.adl_keep(s2, j, c2, _) == List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)) : List<&2, Ad.Lv>}
      %Equal.sym(Nat, Nat.add(n, 1n+j), 1n+Nat.add(n, j), LANat.al.add_succ(n, j)) : {Admission.adl_keep(s2, j, c2, List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, _, c))) == List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)) : List<&2, Ad.Lv>}
      Equal.sym(List<&2, Ad.Lv>, List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)), Admission.adl_keep(s2, j, c2, List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, 1n+Nat.add(n, j), c))), LAList.al.keep_app(s2, j, c2, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)))

def al.admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {Ad.lv.admit.ia(l, q, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}:
  +st = {Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))) : Ad.Sts}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Ad.lv.fresh(Ad.admit.ia.st(Bool.and(Ad.isz(_), Ad.room(l, Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, 0n)))), Ad.le(q, _)), List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Ad.lv.fresh(Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, _)), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))), List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Admission.adl_lives(Ad.preempt(ts), 0n), al.preempt(ts, 0n)) : {List.append(&2, Ad.Lv, _, Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, Ad.preempt(ts), [Ad.Tk{Ad.Ia{}, st}]), 0n), List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, Nat.add(List.length(&2, Ad.Tk, Ad.preempt(ts)), 0n), Ad.Ia{})), al.app(Ad.preempt(ts), Ad.Ia{}, st, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == _ : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ad.Tk, Ad.preempt(ts)), 0n), List.length(&2, Ad.Tk, Ad.preempt(ts)), LANat.al.add_zero(List.length(&2, Ad.Tk, Ad.preempt(ts)))) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, _, Ad.Ia{})) : List<&2, Ad.Lv>}
  %LAList.al.len_pre(ts) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, _, Ad.Ia{})) == List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, Ad.preempt(ts)), Ad.Ia{})) : List<&2, Ad.Lv>}
  {==}

def al.admit_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {Ad.lv.admit.bg(l, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}:
  +st = {Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))) : Ad.Sts}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(_), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Ia{}, Admission.adl_lives(ts, 0n))), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, 0n))), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(_), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, 0n))), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(_), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Ad.lv.held(Admission.adl_lives(ts, 0n)), Ad.held(ts), al.held(ts, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, _))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, st}]), 0n), List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, Nat.add(List.length(&2, Ad.Tk, ts), 0n), Ad.Bg{})), al.app(ts, Ad.Bg{}, st, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Bg{})) == _ : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ad.Tk, ts), 0n), List.length(&2, Ad.Tk, ts), LANat.al.add_zero(List.length(&2, Ad.Tk, ts))) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Bg{})) == List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, _, Ad.Bg{})) : List<&2, Ad.Lv>}
  {==}

# a ticket numbered below the first is not found
def al.find_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j) == None{} : Maybe<&2, Ad.Sts>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Ended{}:
          al.find_none(r, 1n+d, j)

def al.set_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.set(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j, Ad.Held{}) == Admission.adl_lives(ts, 1n+Nat.add(d, j)) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Ended{}:
          al.set_none(r, 1n+d, j)

def al.drop_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j) == Admission.adl_lives(ts, 1n+Nat.add(d, j)) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, LANat.al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Ended{}:
          al.drop_none(r, 1n+d, j)

def al.find0(s: Ad.Sts, c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j) == LALogic.al.st(Some{Ad.Tk{c, s}}) : Maybe<&2, Ad.Sts>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Queued{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Granted{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Held{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Preempted{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Ended{}:
      al.find_none(r, 0n, j)

def al.find1(s: Ad.Sts, c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.find(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}) -> {Ad.lv.find(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j)) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %LANat.al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %LANat.al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %LANat.al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %LANat.al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Ended{}:
      %LANat.al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == LALogic.al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih

# the live controller finds ticket i of the model (numbered from j)
def al.find(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(ts, j), Nat.add(i, j)) == LALogic.al.st(List.get(&2, Ad.Tk, ts, i)) : Maybe<&2, Ad.Sts>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{c, s} <> +r 0n:
      al.find0(s, c, r, j)
    case Ad.Tk{c, s} <> +r 1n++p:
      al.find1(s, c, r, p, j, al.find(r, p, 1n+j))

def al.set0(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat, ne: {Ad.ended(Some{Ad.Tk{c, s}}) == False{} : Bool}) -> {Ad.lv.set(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j, Ad.Held{}) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 0n, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Ended{}:
      LALogic.al.absurd({Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Admission.adl_lives(Ad.Tk{c, Ad.Held{}} <> r, j) : List<&2, Ad.Lv>}, ne)

def al.set1(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}) == Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.set(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j), Ad.Held{}) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 1n+p, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Queued{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Queued{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Granted{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Granted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Held{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Preempted{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Preempted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Ended{}:
      %LANat.al.add_succ(p, j) : {Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      ih

def al.set(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat, ne: {Ad.ended(List.get(&2, Ad.Tk, ts, i)) == False{} : Bool}) -> {Ad.lv.set(Admission.adl_lives(ts, j), Nat.add(i, j), Ad.Held{}) == Admission.adl_lives(Ad.put(ts, i, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{+c, +s} <> +r 0n:
      al.set0(s, c, r, j, ne)
    case Ad.Tk{+c, +s} <> +r 1n++p:
      al.set1(s, c, r, p, j, al.set(r, p, 1n+j, ne))

def al.drop0(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 0n, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LANat.al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Ended{}:
      al.drop_none(r, 0n, j)

def al.drop1(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)) == Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.drop(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j)) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 1n+p, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Queued{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Queued{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Granted{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Granted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Held{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, LANat.al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %LANat.al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Preempted{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Preempted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Ended{}:
      %LANat.al.add_succ(p, j) : {Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      ih

def al.drop(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(ts, j), Nat.add(i, j)) == Admission.adl_lives(Ad.put(ts, i, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{+c, +s} <> +r 0n:
      al.drop0(s, c, r, j)
    case Ad.Tk{+c, +s} <> +r 1n++p:
      al.drop1(s, c, r, p, j, al.drop(r, p, 1n+j))

# ---- the step ----

def al.col(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.collect(LALogic.al.st(m), Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.collect.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.set(Admission.adl_lives(ts, 0n), _, Ad.Held{}), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Held{})}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.set(Admission.adl_lives(ts, 0n), Nat.add(k, 0n), Ad.Held{}), Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), al.set(ts, k, 0n, Equal.trans(Bool, Ad.ended(List.get(&2, Ad.Tk, ts, k)), Ad.ended(Some{Ad.Tk{c, Ad.Granted{}}}), False{}, Equal.cong(Maybe<&2, Ad.Tk>, Bool, x => Ad.ended(x), List.get(&2, Ad.Tk, ts, k), Some{Ad.Tk{c, Ad.Granted{}}}, eq), {==}))) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Held{})}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Held{})), List.length(&2, Ad.Tk, ts), LAList.al.len_put(ts, k, Ad.Held{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.rel(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.release(LALogic.al.st(m), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.release.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
      %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), LAList.al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), LAList.al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.drop(Admission.adl_lives(ts, 0n), _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), LAList.al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.lea(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.leave(LALogic.al.st(m), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.leave.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), LAList.al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), LAList.al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), LAList.al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), LAList.al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.step(s: Ad.St, o: Ad.Op) -> {Ad.Live.step(Admission.adl_live(s), o) == Admission.adl_live(Ad.step(s, o)) : Ad.Live}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{c}:
          match c:
            case Ad.Ia{}:
              %Equal.sym(List<&2, Ad.Lv>, Ad.lv.admit.ia(l, q, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)), Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), al.admit_ia(l, q, ts)) : {Ad.Live{l, q, _, 1n+List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}})) : Ad.Live}
              %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.admit.ia(l, q, ts)), 1n+List.length(&2, Ad.Tk, ts), LAList.al.len_admit_ia(l, q, ts)) : {Ad.Live{l, q, Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), 1n+List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), _} : Ad.Live}
              {==}
            case Ad.Bg{}:
              %Equal.sym(List<&2, Ad.Lv>, Ad.lv.admit.bg(l, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)), Admission.adl_lives(Ad.admit.bg(l, ts), 0n), al.admit_bg(l, ts)) : {Ad.Live{l, q, _, 1n+List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Bg{}})) : Ad.Live}
              %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.admit.bg(l, ts)), 1n+List.length(&2, Ad.Tk, ts), LAList.al.len_app1(ts, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts))))))})) : {Ad.Live{l, q, Admission.adl_lives(Ad.admit.bg(l, ts), 0n), 1n+List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.admit.bg(l, ts), 0n), _} : Ad.Live}
              {==}
        case Ad.Collect{+k}:
          %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.collect(Ad.lv.find(Admission.adl_lives(ts, 0n), _), Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Collect{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), LALogic.al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.collect(_, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Collect{k})) : Ad.Live}
          al.col(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Release{+k}:
          %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.release(Ad.lv.find(Admission.adl_lives(ts, 0n), _), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Release{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), LALogic.al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.release(_, l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Release{k})) : Ad.Live}
          al.rel(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Leave{+k}:
          %LANat.al.add_zero(k) : {Ad.Live{l, q, Ad.lv.leave(Ad.lv.find(Admission.adl_lives(ts, 0n), _), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Leave{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), LALogic.al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.leave(_, l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Leave{k})) : Ad.Live}
          al.lea(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Limit{+l2, q2}:
          %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l2, Admission.adl_lives(ts, 0n)), Admission.adl_lives(Ad.grant(l2, ts), 0n), al.grant(l2, ts, 0n)) : {Ad.Live{l2, q2, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Limit{l2, q2})) : Ad.Live}
          %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l2, ts)), List.length(&2, Ad.Tk, ts), LAList.al.len_grant(l2, ts)) : {Ad.Live{l2, q2, Admission.adl_lives(Ad.grant(l2, ts), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l2, q2, Admission.adl_lives(Ad.grant(l2, ts), 0n), _} : Ad.Live}
          {==}
