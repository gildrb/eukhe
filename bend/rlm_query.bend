# rlm_query: the host's decisions on rlm.query, the paper-style sub-model
# calls of the Python kernel (`await rlm.query(prompt, context)`,
# `rlm.query_batch([...])`: one tool-less model call each). Run as the
# compiled core by bend/ffi_rlm_query.bend (eukhe-bend rules/rlm_query.rs;
# asked by eukhe-core).
#
# plan: a batch of calls is admitted whole or refused. Refusal order: the
# session's query budget (0: none) cannot pay the batch's input bytes, then
# the session's query concurrency cap is already full. An admitted batch
# runs in waves, one after another; a wave is at most the room left under
# the cap, and at most the caller's width (0: as wide as allowed).
# cut: a result past the limit is cut at the end of its longest prefix of
# whole chars that fits the limit in UTF-8 bytes.
# Pure: no IO, no @unsafe.

import Base

# Why a batch is refused
type Refusal is Data:
  OverBudget{total: Nat, left: Nat, budget: Nat}
  Full{cap: Nat}

# The decision on a batch
type Plan is Data:
  Waves{waves: List<&2, Nat>}
  Refused{refusal: Refusal}

# Where a result is cut
type Trim is Data:
  Fits{}
  CutAt{bytes: Nat}

# Plan
# ----

def total.go(xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      total.go(t, Nat.add(acc, x))

# the input bytes of a batch: the sum of its calls' sizes
def total(xs: List<&2, Nat>) -> Nat:
  total.go(xs, 0n)

# u bytes already sent plus t more pass the budget b (0: no budget)
def over(b: Nat, +u: Nat, +t: Nat) -> Bool:
  match b:
    case 0n:
      False{}
    case 1n+k:
      Nat.is_lt(1n+k, Nat.add(u, t))

def width.of(le: Bool, +w: Nat, +room: Nat) -> Nat:
  match le:
    case True{}:
      w
    case False{}:
      room

# the calls of one wave: the room under the cap, at most w (0: no limit)
def width(w: Nat, +room: Nat) -> Nat:
  match w:
    case 0n:
      room
    case 1n++p:
      width.of(Nat.is_le(1n+p, room), 1n+p, room)

def waves.last(r: Nat) -> List<&2, Nat>:
  match r:
    case 0n:
      Nil{}
    case 1n+p:
      [1n+p]

# the waves of n more calls when the open wave holds r calls and m more
# fit in it (a full wave holds r + m + 1)
def waves.go(n: Nat, m: Nat, +r: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      waves.last(r)
    case 1n+np:
      match m:
        case 0n:
          (1n+r) <> waves.go(np, r, 0n)
        case 1n+mp:
          waves.go(np, mp, 1n+r)

# n calls in waves of k, in order; the last wave holds what is left
def waves(n: Nat, k: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      waves.last(n)
    case 1n+bp:
      waves.go(n, bp, 0n)

def plan.full(full: Bool, +c: Nat, +r: Nat, +w: Nat, +n: Nat) -> Plan:
  match full:
    case True{}:
      Refused{Full{c}}
    case False{}:
      Waves{waves(n, width(w, Nat.sub(c, r)))}

def plan.budget(over: Bool, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +t: Nat, +n: Nat) -> Plan:
  match over:
    case True{}:
      Refused{OverBudget{t, Nat.sub(b, u), b}}
    case False{}:
      plan.full(Nat.is_le(c, r), c, r, w, n)

# the decision on a batch whose calls send sizes bytes each, r query
# calls of the session running under the cap c, the caller's width w, the
# budget b (0: none) of which u bytes are spent
def plan(+r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>) -> Plan:
  +t = total(sizes)
  plan.budget(over(b, u, t), r, c, w, b, u, t, List.length(&2, Nat, sizes))

# the text of a refusal
def text(f: Refusal) -> String:
  match f:
    case OverBudget{t, l, b}:
      "rlm.query needs " ++ Nat.show(t) ++ " bytes of input; the session's query budget has " ++ Nat.show(l) ++ " of " ++ Nat.show(b) ++ " bytes left (rlm.queryBudgetBytes)"
    case Full{c}:
      "rlm.query concurrency limit " ++ Nat.show(c) ++ " is already full"

# Cut
# ---

def bytes.of(a: Bool, b: Bool, c: Bool) -> Nat:
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

# the UTF-8 bytes of a char: 1 below 0x80, 2 below 0x800, 3 below 0x10000,
# else 4
def bytes(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      bytes.of(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

def cut.last(fit: Bool, at: Nat) -> Trim:
  match fit:
    case True{}:
      Fits{}
    case False{}:
      CutAt{at}

# s: the chars after the current one, which takes w bytes; fit: w is at
# most room, the bytes left under the limit; at: the bytes of the chars
# before the current one (one flat loop)
def cut.go(s: String, fit: Bool, +w: Nat, +room: Nat, +at: Nat) -> Trim:
  match s:
    case SNil{}:
      cut.last(fit, at)
    case SCon{c, r}:
      match fit:
        case True{}:
          +v = bytes(c)
          +left = Nat.sub(room, w)
          cut.go(r, Nat.is_le(v, left), v, left, Nat.add(at, w))
        case False{}:
          CutAt{at}

# where the text t is cut under the limit of m bytes
def cut(+m: Nat, t: String) -> Trim:
  match t:
    case SNil{}:
      Fits{}
    case SCon{c, r}:
      +v = bytes(c)
      cut.go(r, Nat.is_le(v, m), v, m, 0n)
