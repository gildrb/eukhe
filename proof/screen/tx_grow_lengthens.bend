# eukhe: the proof of LAW tx_grow_lengthens
#
# PROOF: the model's length max(l, min(l + k, c)) is the requirement's case
# split (l + k when it fits under c; else c, or l past c) for every cap c,
# by induction on l and c (grow.cap); so for c = 2^32 - 1 too. Then, block
# by block along the edit (induction on the blocks), a block whose id is x
# grows (grow1) as tx_grew.at asks of each state, and one of another id is
# kept.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/events.bend as ScreenEvents
import ./base/events.bend as LAScreenEvents

def grow.succ(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

# 1 + the grown length of l under c is the grown length of 1 + l under 1 + c
def grow.cap_succ(fits: Bool, past: Bool, +l: Nat, +k: Nat, +c: Nat) -> {1n+ScreenEvents.tx_grown.of(fits, past, l, k, c) == ScreenEvents.tx_grown.of(fits, past, 1n+l, k, 1n+c) : Nat}:
  match fits past:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def grow.min_succ(fits: Bool, +k: Nat, +c: Nat) -> {1n+ScreenEvents.tx_grown.of(fits, False{}, 0n, k, c) == ScreenEvents.tx_grown.of(fits, False{}, 0n, 1n+k, 1n+c) : Nat}:
  match fits:
    case True{}:
      {==}
    case False{}:
      {==}

# from an empty block: min(k, c)
def grow.min(+k: Nat, +c: Nat) -> {Nat.min(k, c) == ScreenEvents.tx_grown.of(Nat.is_le(k, c), False{}, 0n, k, c) : Nat}:
  match k c:
    case 0n 0n:
      {==}
    case 0n 1n+cp:
      {==}
    case 1n+kp 0n:
      {==}
    case 1n++kp 1n++cp:
      Equal.trans(Nat, 1n+Nat.min(kp, cp), 1n+ScreenEvents.tx_grown.of(Nat.is_le(kp, cp), False{}, 0n, kp, cp), ScreenEvents.tx_grown.of(Nat.is_le(kp, cp), False{}, 0n, 1n+kp, 1n+cp), grow.succ(Nat.min(kp, cp), ScreenEvents.tx_grown.of(Nat.is_le(kp, cp), False{}, 0n, kp, cp), grow.min(kp, cp)), grow.min_succ(Nat.is_le(kp, cp), kp, cp))

# the model's capped growth is the requirement's, under any cap c
def grow.cap(+l: Nat, +k: Nat, +c: Nat) -> {Nat.max(l, Nat.min(Nat.add(l, k), c)) == ScreenEvents.tx_grown.of(Nat.is_le(Nat.add(l, k), c), Nat.is_lt(c, l), l, k, c) : Nat}:
  match l c:
    case 0n 0n:
      grow.min(k, 0n)
    case 0n 1n+cp:
      grow.min(k, 1n+cp)
    case 1n+lp 0n:
      {==}
    case 1n++lp 1n++cp:
      Equal.trans(Nat, 1n+Nat.max(lp, Nat.min(Nat.add(lp, k), cp)), 1n+ScreenEvents.tx_grown.of(Nat.is_le(Nat.add(lp, k), cp), Nat.is_lt(cp, lp), lp, k, cp), ScreenEvents.tx_grown.of(Nat.is_le(Nat.add(lp, k), cp), Nat.is_lt(cp, lp), 1n+lp, k, 1n+cp), grow.succ(Nat.max(lp, Nat.min(Nat.add(lp, k), cp)), ScreenEvents.tx_grown.of(Nat.is_le(Nat.add(lp, k), cp), Nat.is_lt(cp, lp), lp, k, cp), grow.cap(lp, k, cp)), grow.cap_succ(Nat.is_le(Nat.add(lp, k), cp), Nat.is_lt(cp, lp), lp, k, cp))

def grow.len(+l: Nat, +k: Nat) -> {Nat.is_eq(Nat.max(l, Nat.min(Nat.add(l, k), 4294967295n)), ScreenEvents.tx_grown(l, k)) == True{} : Bool}:
  %grow.cap(l, k, 4294967295n) : {Nat.is_eq(Nat.max(l, Nat.min(Nat.add(l, k), 4294967295n)), _) == True{} : Bool}
  LAScreenEvents.ev.t(Nat.max(l, Nat.min(Nat.add(l, k), 4294967295n)))

# a block of id x after grow1
def grow.hit(+i: Nat, +s: Sc.St, +l: Nat, +x: Nat, +k: Nat, e: {Nat.is_eq(i, x) == True{} : Bool}) -> {ScreenEvents.tx_grew.blk(x, k, Sc.Blk{i, s, l}, Sc.edit.one(Sc.Blk{i, s, l}, Some{k})) == True{} : Bool}:
  match s:
    case Sc.Active{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_grew.at(_, i, Sc.Active{}, l, i, Sc.Active{}, Nat.max(l, Nat.min(Nat.add(l, k), 4294967295n)), k) == True{} : Bool}
      LAScreenEvents.ev.and_t(Nat.is_eq(i, i), Nat.is_eq(Nat.max(l, Nat.min(Nat.add(l, k), 4294967295n)), ScreenEvents.tx_grown(l, k)), LAScreenEvents.ev.t(i), grow.len(l, k))
    case Sc.Final{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_grew.at(_, i, Sc.Final{}, l, i, Sc.Final{}, l, k) == True{} : Bool}
      LAScreenEvents.ev.and_t(Nat.is_eq(i, i), Nat.is_eq(l, l), LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l))
    case Sc.Comm{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_grew.at(_, i, Sc.Comm{}, l, i, Sc.Comm{}, l, k) == True{} : Bool}
      LAScreenEvents.ev.and_t(Nat.is_eq(i, i), Nat.is_eq(l, l), LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l))

# a block of another id, kept
def grow.miss(+i: Nat, +s: Sc.St, +l: Nat, +x: Nat, +k: Nat, e: {Nat.is_eq(i, x) == False{} : Bool}) -> {ScreenEvents.tx_grew.blk(x, k, Sc.Blk{i, s, l}, Sc.Blk{i, s, l}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(i, x), False{}, e) : {ScreenEvents.tx_grew.at(_, i, s, l, i, s, l, k) == True{} : Bool}
  LAScreenEvents.ev.and3(Nat.is_eq(i, i), ScreenEvents.tx_st_eq(s, s), Nat.is_eq(l, l), LAScreenEvents.ev.t(i), LAScreenEvents.ev.st_t(s), LAScreenEvents.ev.t(l))

def grow.at(+i: Nat, +s: Sc.St, +l: Nat, +br: List<&2, Sc.Blk>, +x: Nat, +k: Nat, hit: Bool, e: {Nat.is_eq(i, x) == hit : Bool}, ih: {ScreenEvents.tx_grew(x, k, br, Sc.edit.go(br, x, Some{k}, Sc.bid.at(br, x))) == True{} : Bool}) -> {ScreenEvents.tx_grew(x, k, Sc.Blk{i, s, l} <> br, Sc.edit.go(Sc.Blk{i, s, l} <> br, x, Some{k}, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      LAScreenEvents.ev.and_t(ScreenEvents.tx_grew.blk(x, k, Sc.Blk{i, s, l}, Sc.edit.one(Sc.Blk{i, s, l}, Some{k})), ScreenEvents.tx_grew(x, k, br, Sc.edit.go(br, x, Some{k}, Sc.bid.at(br, x))), grow.hit(i, s, l, x, k, e), ih)
    case False{}:
      LAScreenEvents.ev.and_t(ScreenEvents.tx_grew.blk(x, k, Sc.Blk{i, s, l}, Sc.Blk{i, s, l}), ScreenEvents.tx_grew(x, k, br, Sc.edit.go(br, x, Some{k}, Sc.bid.at(br, x))), grow.miss(i, s, l, x, k, e), ih)

def grow.blocks(bs: List<&2, Sc.Blk>, +x: Nat, +k: Nat) -> {ScreenEvents.tx_grew(x, k, bs, Sc.edit.go(bs, x, Some{k}, Sc.bid.at(bs, x))) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, s, l}:
          grow.at(i, s, l, br, x, k, Nat.is_eq(i, x), {==}, grow.blocks(br, x, k))

def grow.law(+t: Sc.Tx, +x: Nat, +k: Nat) -> {ScreenEvents.tx_grew(x, k, Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Grow{x, k}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      grow.blocks(bs, x, k)

def ScreenEvents.tx_grow_lengthens(t, x, k):
  grow.law(t, x, k)
