# family: who may spawn a subagent (rlm.spawn, rlm.spawn_batch, the
# workflow tool's agent(), the factory's states). Run as the compiled core
# by bend/ffi_family.bend (eukhe-bend rules/family.rs; asked by eukhe-core
# durable/children/requests.rs before and inside the admitting commit).
#
# A spawn names its reason (`why`): parallel, isolate, tools or user. A
# batch is decided whole: every reason allowed, the caller below the
# recursion bound, the family's running subagents plus the batch within the
# cap (0: no cap). Refusal order: a missing reason, the depth, the cap.
# Pure: no IO, no @unsafe.

import Base

# The reason of a spawn
type Why is Data:
  WParallel{}
  WIsolate{}
  WTools{}
  WUser{}

# Why a batch is refused
type Refusal is Data:
  DepthLimit{}
  FamilyFull{cap: Nat}
  NoReason{index: Nat}

# The decision on a batch
type Verdict is Data:
  Admit{child_depth: Nat}
  Refuse{refusal: Refusal}

# Reasons
# -------

def reason.of(p: Bool, i: Bool, t: Bool, u: Bool) -> Maybe<&2, Why>:
  match p:
    case True{}:
      Some{WParallel{}}
    case False{}:
      match i:
        case True{}:
          Some{WIsolate{}}
        case False{}:
          match t:
            case True{}:
              Some{WTools{}}
            case False{}:
              match u:
                case True{}:
                  Some{WUser{}}
                case False{}:
                  None{}

# the reason a why text names, if any
def reason(+s: String) -> Maybe<&2, Why>:
  reason.of(String.eq(s, "parallel"), String.eq(s, "isolate"), String.eq(s, "tools"), String.eq(s, "user"))

def bad.at(m: Maybe<&2, Why>, +i: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{i}
    case Some{w}:
      r

# the index of the first why that names no reason, counting from i
def bad(ws: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match ws:
    case Nil{}:
      None{}
    case w <> rest:
      bad.at(reason(w), i, bad(rest, 1n+i))

# Decision
# --------

def full.of(c: Nat, +used: Nat) -> Bool:
  match c:
    case 0n:
      False{}
    case 1n+k:
      Bool.not(Nat.is_le(used, 1n+k))

# the family is full: a cap, and the running subagents plus n exceed it
def full(+r: Nat, +c: Nat, +n: Nat) -> Bool:
  full.of(c, Nat.add(r, n))

def decide.cap(over: Bool, +c: Nat, +d: Nat) -> Verdict:
  match over:
    case True{}:
      Refuse{FamilyFull{c}}
    case False{}:
      Admit{1n+d}

def decide.depth(deep: Bool, +d: Nat, +r: Nat, +c: Nat, +n: Nat) -> Verdict:
  match deep:
    case True{}:
      Refuse{DepthLimit{}}
    case False{}:
      decide.cap(full(r, c, n), c, d)

def decide.why(b: Maybe<&2, Nat>, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat) -> Verdict:
  match b:
    case Some{i}:
      Refuse{NoReason{i}}
    case None{}:
      decide.depth(Nat.is_le(m, d), d, r, c, n)

# the decision on a batch whose whys are ws, asked at depth d under the
# bound m, with r subagents of the family running under the cap c
def decide(+d: Nat, +m: Nat, +r: Nat, +c: Nat, +ws: List<&2, String>) -> Verdict:
  decide.why(bad(ws, 0n), d, m, r, c, List.length(&2, String, ws))

# Texts
# -----

def why_rule() -> String:
  "why must be \"parallel\" (independent tasks run at once), \"isolate\" (the work would bloat this context; only a compact result comes back), \"tools\" (the task needs a tool set or instructions that conflict with this agent's) or \"user\" (the user asked for a subagent); otherwise do the work in this loop"

# the text of a refusal at depth d under the bound m
def text(+d: Nat, +m: Nat, f: Refusal) -> String:
  match f:
    case DepthLimit{}:
      "RLM recursion depth limit reached (RLM_DEPTH=" ++ Nat.show(d) ++ ", RLM_MAX_DEPTH=" ++ Nat.show(m) ++ ")"
    case FamilyFull{c}:
      "subagent concurrency limit " ++ Nat.show(c) ++ " is already full"
    case NoReason{i}:
      "rlm.spawn task " ++ Nat.show(i) ++ " has no allowed why: " ++ why_rule()
