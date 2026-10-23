# eukhe: lemmas the proofs of area admission share: list

import Base
import ../../../bend/admission.bend as Ad
import ../../../laws/admission.bend as Admission

# Lengths
# -------

def al.len_put(ts: List<&2, Ad.Tk>, i: Nat, +x: Ad.Sts) -> {List.length(&2, Ad.Tk, Ad.put(ts, i, x)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> r:
      match i:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.put(r, p, x)), List.length(&2, Ad.Tk, r), al.len_put(r, p, x))

def al.len_mark_at(b: Bool, c: Ad.Cls, h: Ad.Tk, +r: List<&2, Ad.Tk>, -m: List<&2, Ad.Tk>, ih: {List.length(&2, Ad.Tk, m) == List.length(&2, Ad.Tk, r) : Nat}) -> {List.length(&2, Ad.Tk, Ad.mark.at(b, c, h, r, m)) == 1n+List.length(&2, Ad.Tk, r) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, m), List.length(&2, Ad.Tk, r), ih)

def al.len_mark(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.mark(c, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      al.len_mark_at(Ad.hit(Ad.Waiting{}, c, h), c, h, r, Ad.mark(c, r), al.len_mark(c, r))

def al.len_grant_go(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.grant.go(n, d, l, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{+c}:
      Equal.trans(Nat, List.length(&2, Ad.Tk, Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts))), List.length(&2, Ad.Tk, Ad.mark(c, ts)), List.length(&2, Ad.Tk, ts), al.len_grant_go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), al.len_mark(c, ts))

def al.len_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.grant(l, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  al.len_grant_go(Ad.waits(ts), Ad.pick(l, ts), l, ts)

def al.len_pre(ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.preempt(ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.preempt(r)), List.length(&2, Ad.Tk, r), al.len_pre(r))

def al.len_app1(a: List<&2, Ad.Tk>, -x: Ad.Tk) -> {List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, a, [x])) == 1n+List.length(&2, Ad.Tk, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, r, [x])), 1n+List.length(&2, Ad.Tk, r), al.len_app1(r, x))

def al.keep_app(s: Ad.Sts, +k: Nat, +c: Ad.Cls, a: List<&2, Ad.Lv>, b: List<&2, Ad.Lv>) -> {List.append(&2, Ad.Lv, Admission.adl_keep(s, k, c, a), b) == Admission.adl_keep(s, k, c, List.append(&2, Ad.Lv, a, b)) : List<&2, Ad.Lv>}:
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

# Lengths of an admit
def al.len_admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.admit.ia(l, q, ts)) == 1n+List.length(&2, Ad.Tk, ts) : Nat}:
  +x = {Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))} : Ad.Tk}
  Equal.trans(Nat, List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])), 1n+List.length(&2, Ad.Tk, Ad.preempt(ts)), 1n+List.length(&2, Ad.Tk, ts), al.len_app1(Ad.preempt(ts), x), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.preempt(ts)), List.length(&2, Ad.Tk, ts), al.len_pre(ts)))
