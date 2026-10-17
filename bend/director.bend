# director: the model of the Director stack (docs/harness.md, S5). The
# agent loop asks the stack what to do after each model turn. A Director
# is one layer: a plan, a goal, a reminder, a forced tool call. Layers
# stack and nest. The top layer decides first; each layer gives one
# verdict, which the adversary picks:
#
# - Pass: the next layer down decides.
# - Go: the loop goes on. It costs the layer one unit of its budget.
# - Halt: the loop stops and hands back to the user.
# - Stack{l}: the layer adds l on top, and the loop goes on. It costs the
#   layer one unit of its budget. A full stack (cap layers) fails.
# - Pop: the layer removes itself; the next layer down decides.
# - Fail: the loop stops with a failure.
#
# A layer with no budget left that says Go or Push halts the loop. With
# no layer left to decide, the loop hands back to the user. The loop also
# has a global budget of steps: when it is 0, a Cont yields.
#
# The stack lives in the session tree (bend/tree.bend): encode writes it
# as nodes, decode reads it back. So a rewind of the tree restores the
# stack, and a resume reads the same stack.

import Base
import ./tree.bend as T

# A layer: its kind (plan, goal, reminder, forced call, ...) and the
# loop steps it may still ask for
type Layer is Data:
  Layer{kind: Nat, budget: Nat}

type Verdict is Data:
  Defer{}
  Again{}
  Yield{}
  Stack{l: Layer}
  Leave{}
  Abort{}

# What one decision gives the loop
type Out is Data:
  Cont{}    # the loop goes on
  Hand{}    # the loop stops; the user has control
  Failed{}  # the loop stops with a failure

# A decision: what the loop does, and the stack after it (top first)
type Dec is Data:
  Dec{out: Out, stack: List<&2, Layer>}

def Dec.out(d: Dec) -> Out:
  match d:
    case Dec{o, s}:
      o

def Dec.stack(d: Dec) -> List<&2, Layer>:
  match d:
    case Dec{o, s}:
      s

def Layer.budget(l: Layer) -> Nat:
  match l:
    case Layer{k, b}:
      b

# put l back on top of a decision's stack
def under(+l: Layer, d: Dec) -> Dec:
  match d:
    case Dec{o, s}:
      Dec{o, l <> s}

# a Stack of n onto the stack s under l, with room telling whether the
# stack has fewer than cap layers
def push.at(room: Bool, +l: Layer, +n: Layer, +rest: List<&2, Layer>) -> Dec:
  match room:
    case True{}:
      Dec{Cont{}, n <> l <> rest}
    case False{}:
      Dec{Failed{}, l <> rest}

# What layer l does with its verdict v, under `above` layers and above the
# layers rest; d is the decision of rest on the verdicts below v. A Stack
# needs room in the whole stack: above + 1 + len(rest) layers now.
def pick(v: Verdict, l: Layer, +rest: List<&2, Layer>, +cap: Nat, +above: Nat, d: Dec) -> Dec:
  match v:
    case Defer{}:
      under(l, d)
    case Again{}:
      match l:
        case Layer{k, b}:
          match b:
            case 0n:
              Dec{Hand{}, Layer{k, 0n} <> rest}
            case 1n+c:
              Dec{Cont{}, Layer{k, c} <> rest}
    case Yield{}:
      Dec{Hand{}, l <> rest}
    case Stack{n}:
      match l:
        case Layer{k, b}:
          match b:
            case 0n:
              Dec{Hand{}, Layer{k, 0n} <> rest}
            case 1n+c:
              push.at(Nat.is_lt(Nat.add(above, 1n+List.length(&2, Layer, rest)), cap), Layer{k, c}, n, rest)
    case Leave{}:
      d
    case Abort{}:
      Dec{Failed{}, l <> rest}

# One decision of the stack s (top first) under `above` layers that
# deferred. vs holds each layer's verdict, top first; a layer with no
# verdict left defers.
def decide.go(s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat, +above: Nat) -> Dec:
  match s:
    case Nil{}:
      Dec{Hand{}, Nil{}}
    case l <> +rest:
      match vs:
        case Nil{}:
          under(l, decide.go(rest, Nil{}, cap, 1n+above))
        case v <> vr:
          pick(v, l, rest, cap, above, decide.go(rest, vr, cap, 1n+above))

# One decision of the whole stack
def decide(+s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat) -> Dec:
  decide.go(s, vs, cap, 0n)

# The loop
# --------

# The loop's state: the global budget left, the stack, and how it ended
# (None while it runs)
type Loop is Data:
  Loop{left: Nat, stack: List<&2, Layer>, end: Maybe<&2, Out>}

def Loop.end(l: Loop) -> Maybe<&2, Out>:
  match l:
    case Loop{n, s, e}:
      e

def Loop.stack(l: Loop) -> List<&2, Layer>:
  match l:
    case Loop{n, s, e}:
      s

# the loop that goes on with n steps left: with none left it yields
def cont(n: Nat, s: List<&2, Layer>) -> Loop:
  match n:
    case 0n:
      Loop{0n, s, Some{Hand{}}}
    case 1n+m:
      Loop{m, s, None{}}

# the loop after a decision d, with n steps left
def after(+n: Nat, d: Dec) -> Loop:
  match d:
    case Dec{o, s}:
      match o:
        case Cont{}:
          cont(n, s)
        case Hand{}:
          Loop{n, s, Some{Hand{}}}
        case Failed{}:
          Loop{n, s, Some{Failed{}}}

# one loop step: the stack decides on the verdicts vs
def tick(+cap: Nat, l: Loop, vs: List<&2, Verdict>) -> Loop:
  match l:
    case Loop{n, s, e}:
      match e:
        case None{}:
          after(n, decide(s, vs, cap))
        case Some{x}:
          Loop{n, s, Some{x}}

# the loop after the verdicts of each step
def run(vss: List<&2, List<&2, Verdict>>, +cap: Nat, l: Loop) -> Loop:
  match vss:
    case Nil{}:
      l
    case vs <> rest:
      run(rest, cap, tick(cap, l, vs))

def ended(l: Loop) -> Bool:
  Maybe.is_some(&2, Out, Loop.end(l))

# The stack in the session tree
# -----------------------------
# Each layer is two nodes: its kind, and under it its budget. The bottom
# layer's kind hangs under the root; each layer's kind hangs under the
# kind of the layer below it. Keys count up from the bottom: layer i
# (0 = bottom) has keys 2i + 1 (kind) and 2i + 2 (budget).

# the key of the kind node of the layer above n layers
def kind.key(n: Nat) -> Nat:
  1n+Nat.double(n)

# the parent of that kind node
def kind.parent(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      1n+Nat.double(m)

# the nodes of a stack (top first), in ascending key order
def encode(s: List<&2, Layer>) -> List<&2, T.Ent>:
  match s:
    case Nil{}:
      Nil{}
    case l <> +rest:
      match l:
        case Layer{k, b}:
          +n = List.length(&2, Layer, rest)
          List.append(&2, T.Ent, encode(rest), [T.Ent{kind.key(n), kind.parent(n), k}, T.Ent{1n+kind.key(n), kind.key(n), b}])

# read layers from nodes in ascending key order, two nodes a layer, onto
# acc (the layers below, top first)
def decode.go(t: List<&2, T.Ent>, acc: List<&2, Layer>) -> List<&2, Layer>:
  match t:
    case Nil{}:
      acc
    case a <> rest:
      match rest:
        case Nil{}:
          acc
        case b <> more:
          decode.go(more, Layer{T.Ent.v(a), T.Ent.v(b)} <> acc)

# the stack (top first) the tree holds
def decode(t: List<&2, T.Ent>) -> List<&2, Layer>:
  decode.go(t, Nil{})
