# rlm_query (spec): the admission of an rlm.query batch and the cut of a
# result, restated without the code (bend/rlm_query.bend). The laws of area
# rlm_query (laws/rlm_query.bend) state that the code refines it. A spec:
# the shipped code never calls it.
#
# S1: a batch whose input bytes, with the bytes the session's queries
#     already sent, pass a budget (0: no budget) is refused for the budget,
#     naming the batch's bytes, what is left of the budget (0 when spent)
#     and the budget.
# S2: else a session whose running queries fill the cap is refused for it.
# S3: else the batch runs in waves of k calls, k the room under the cap
#     (the cap less the running calls), at most the caller's width when
#     it gives one (not 0): n div k waves of k, then one of n mod k when
#     that is not 0.
# S4: a result fits when its UTF-8 bytes are at most the limit; else it is
#     cut after the longest prefix of its chars whose UTF-8 bytes are at
#     most the limit. A char takes 1 byte below 0x80, 2 below 0x800, 3
#     below 0x10000, else 4.

import Base
import ../../bend/rlm_query.bend as Rq

# S1: the budget
# --------------

# the sum of xs
def total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(x, total(t))

# a budget b is set, and u bytes spent plus t more pass it
def over_budget(+b: Nat, +u: Nat, +t: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, b), Nat.is_lt(b, Nat.add(u, t)))

# S3: the waves
# -------------

def wave.of(any: Bool, +w: Nat, +room: Nat) -> Nat:
  match any:
    case True{}:
      room
    case False{}:
      Nat.min(w, room)

# the calls of a wave: the room under the cap, at most the width w when
# w is not 0
def wave(+w: Nat, +room: Nat) -> Nat:
  wave.of(Nat.is_eq(w, 0n), w, room)

# d copies of k
def copies(d: Nat, +k: Nat) -> List<&2, Nat>:
  match d:
    case 0n:
      Nil{}
    case 1n+p:
      k <> copies(p, k)

# the wave of what is left: none when nothing is
def rest(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      [1n+p]

# n calls in waves of k
def waves(+n: Nat, +k: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, copies(Nat.div(n, k), k), rest(Nat.mod(n, k)))

# S1-S3: the decision
# -------------------

def plan.cap(full: Bool, +c: Nat, +r: Nat, +w: Nat, +n: Nat) -> Rq.Plan:
  match full:
    case True{}:
      Rq.Refused{Rq.Full{c}}
    case False{}:
      Rq.Waves{waves(n, wave(w, Nat.sub(c, r)))}

def plan.of(over: Bool, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>) -> Rq.Plan:
  match over:
    case True{}:
      Rq.Refused{Rq.OverBudget{total(sizes), Nat.sub(b, u), b}}
    case False{}:
      plan.cap(Nat.is_le(c, r), c, r, w, List.length(&2, Nat, sizes))

# the decision on the batch sizes, r running under the cap c, the width w,
# the budget b of which u is spent
def plan(+r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>) -> Rq.Plan:
  plan.of(over_budget(b, u, total(sizes)), r, c, w, b, u, sizes)

# S4: the cut
# -----------

def width.of(a: Bool, b: Bool, c: Bool) -> Nat:
  match a:
    case True{}:
      1n
    case False{}:
      match b:
        case True{}:
          2n
        case False{}:
          match c:
            case True{}:
              3n
            case False{}:
              4n

# the UTF-8 bytes of a char
def width(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      width.of(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

# the UTF-8 bytes of a text
def utf8(t: String) -> Nat:
  match t:
    case SNil{}:
      0n
    case SCon{c, r}:
      Nat.add(width(c), utf8(r))

# c before each of ps
def heads(+c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, q}:
      SCon{c, p} <> heads(c, q)

# every prefix of t, the empty one first, shortest first
def prefixes(t: String) -> List<&2, String>:
  match t:
    case SNil{}:
      [""]
    case SCon{c, r}:
      "" <> heads(c, prefixes(r))

def longest.pick(ok: Bool, +n: Nat, +best: Nat) -> Nat:
  match ok:
    case True{}:
      n
    case False{}:
      best

# the UTF-8 bytes of the last of ps within m bytes (best when none is)
def longest(+m: Nat, ps: List<&2, String>, +best: Nat) -> Nat:
  match ps:
    case Nil{}:
      best
    case Con{+p, q}:
      longest(m, q, longest.pick(Nat.is_le(utf8(p), m), utf8(p), best))

def cut.of(fits: Bool, +m: Nat, +t: String) -> Rq.Trim:
  match fits:
    case True{}:
      Rq.Fits{}
    case False{}:
      Rq.CutAt{longest(m, prefixes(t), 0n)}

# where t is cut under the limit of m bytes
def cut(+m: Nat, +t: String) -> Rq.Trim:
  cut.of(Nat.is_le(utf8(t), m), m, t)
