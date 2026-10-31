# family (spec): when a subagent family may grow, restated without the
# admission code (bend/family.bend). The laws of area family
# (laws/family.bend) state that the code refines it. A spec: the shipped
# code never calls it.
#
# S1: a spawn names an allowed reason: one of the four texts of
#     `reasons` (parallel, isolate, tools, user), compared whole.
# S2: the family tree's depth never exceeds the bound: a caller at depth d
#     under the bound m spawns at depth d + 1, only when d + 1 <= m.
# S3: the running children never exceed the cap: with a cap c (0: none),
#     r running plus the n of the batch stay at most c.
# S4: a batch is one decision: all of it admits, or none of it.
# S5: a refused batch names the first rule it breaks, in order: a spawn
#     without an allowed reason (the first such index), the depth, the cap.

import Base
import ../../bend/family.bend as F

# S1: reasons
# -----------

# the reasons a spawn may name
def reasons() -> List<&2, String>:
  ["parallel", "isolate", "tools", "user"]

def allowed.in(+s: String, rs: List<&2, String>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(s, x), allowed.in(s, t))

# s is one of the reasons
def allowed(+s: String) -> Bool:
  allowed.in(s, reasons())

# every why of ws is a reason
def all_ok(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case w <> t:
      Bool.and(allowed(w), all_ok(t))

def first_bad.of(ok: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{i}

# the index (from i) of the first why of ws that is no reason
def first_bad(ws: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match ws:
    case Nil{}:
      None{}
    case w <> t:
      first_bad.of(allowed(w), i, first_bad(t, 1n+i))

# S2, S3: the bounds
# ------------------

# a caller at depth d has reached the bound m
def deep(+d: Nat, +m: Nat) -> Bool:
  Nat.is_le(m, d)

# r running plus n more fit the cap c (0: no cap)
def cap_ok(+r: Nat, +c: Nat, +n: Nat) -> Bool:
  Bool.or(Nat.is_eq(c, 0n), Nat.is_le(Nat.add(r, n), c))

# S4: the batch ws is admitted whole
def admits(+d: Nat, +m: Nat, +r: Nat, +c: Nat, +ws: List<&2, String>) -> Bool:
  Bool.and(all_ok(ws), Bool.and(Bool.not(deep(d, m)), cap_ok(r, c, List.length(&2, String, ws))))

# S5: the decision
# ----------------

def verdict.cap(ok: Bool, +c: Nat, +d: Nat) -> F.Verdict:
  match ok:
    case True{}:
      F.Admit{1n+d}
    case False{}:
      F.Refuse{F.FamilyFull{c}}

def verdict.deep(x: Bool, +d: Nat, +r: Nat, +c: Nat, +n: Nat) -> F.Verdict:
  match x:
    case True{}:
      F.Refuse{F.DepthLimit{}}
    case False{}:
      verdict.cap(cap_ok(r, c, n), c, d)

def verdict.of(b: Maybe<&2, Nat>, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat) -> F.Verdict:
  match b:
    case Some{i}:
      F.Refuse{F.NoReason{i}}
    case None{}:
      verdict.deep(deep(d, m), d, r, c, n)

# the decision on the batch ws at depth d under the bound m, r running
# under the cap c
def verdict(+d: Nat, +m: Nat, +r: Nat, +c: Nat, +ws: List<&2, String>) -> F.Verdict:
  verdict.of(first_bad(ws, 0n), d, m, r, c, List.length(&2, String, ws))
