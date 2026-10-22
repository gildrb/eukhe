# director: the model of the Director stack (docs/control.md, S5), the
# rule the Rust code runs (crates/eukhe-core/src/durable/directors). The
# agent loop asks the stack what to do after each model turn. A Director
# is one layer: a goal, an autonomous run, a reminder, a forced tool call.
# Layers stack and nest. The top layer decides first; each layer gives one
# verdict, which the adversary picks:
#
# - Defer: the layer stays; the next layer down decides.
# - Again: the loop goes on. It costs the layer one unit of its budget.
# - Yield: the loop stops and hands back to the user.
# - Stack{l}: the layer adds l on top, and the loop goes on. It costs the
#   layer one unit of its budget. A stack that holds cap layers already
#   (counting every layer, those above the deciding one too) fails.
# - Leave: the layer removes itself; the next layer down decides.
# - Abort: the loop stops with a failure.
# - Lead: a reminder that leads the next continuation. It leaves with the
#   continuation it leads: when the loop goes on it leaves, and when the
#   loop ends it stays for the next run. Either way the next layer down
#   decides.
#
# A layer with no budget left that says Again or Stack yields. With no
# layer left to decide, or no verdict left (a missing verdict defers), the
# loop hands back to the user. The loop also has a global budget of
# steps: a continue with none left yields.
#
# Kinds are opaque numbers: the Rust code numbers the distinct layers of
# one step and maps the numbers back. Budgets, the global budget and the
# cap are counts the Rust code saturates at 2^48-1 before it calls the
# model; the model only lowers a budget by one and compares the cap with
# the stack's length, so no value ever grows past its input.
#
# The stack lives in the session tree (bend/tree.bend): encode writes it
# as nodes, decode reads it back. So a rewind of the tree restores the
# stack, and a resume reads the same stack.

import Base
import ./tree.bend as T

# A layer: its kind (goal, autonomous run, reminder, forced call, ...)
# and the loop steps it may still ask for
type Layer is Data:
  Layer{kind: Nat, budget: Nat}

type Verdict is Data:
  Defer{}
  Again{}
  Yield{}
  Stack{l: Layer}
  Leave{}
  Abort{}
  Lead{}

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

# an Again of l above the layers rest
def spend(l: Layer, +rest: List<&2, Layer>) -> Dec:
  match l:
    case Layer{k, b}:
      match b:
        case 0n:
          Dec{Hand{}, Layer{k, 0n} <> rest}
        case 1n+c:
          Dec{Cont{}, Layer{k, c} <> rest}

# a Stack of n by l (its budget already spent) above the layers rest;
# room tells whether the whole stack holds fewer than cap layers
def push.at(room: Bool, +l: Layer, +n: Layer, +rest: List<&2, Layer>) -> Dec:
  match room:
    case True{}:
      Dec{Cont{}, n <> l <> rest}
    case False{}:
      Dec{Failed{}, l <> rest}

# a Stack of n by l above the layers rest
def push(l: Layer, +n: Layer, +rest: List<&2, Layer>, +room: Bool) -> Dec:
  match l:
    case Layer{k, b}:
      match b:
        case 0n:
          Dec{Hand{}, Layer{k, 0n} <> rest}
        case 1n+c:
          push.at(room, Layer{k, c}, n, rest)

# a Lead of l over the decision d of the layers below: l stays on top when
# stay holds, else it leaves
def lead(stay: Bool, +l: Layer, d: Dec) -> Dec:
  match stay:
    case True{}:
      under(l, d)
    case False{}:
      d

# One decision of the stack s (top first) on the verdicts vs (top first; a
# layer with no verdict left defers). room tells whether the whole stack
# holds fewer than cap layers; stay tells whether a layer that leads stays
# (the loop ends) or leaves (the loop goes on). Only the deciding layer's
# verdict is looked at below the layers that defer, leave or lead.
def decide.go(s: List<&2, Layer>, vs: List<&2, Verdict>, +room: Bool, +stay: Bool) -> Dec:
  match s:
    case Nil{}:
      Dec{Hand{}, Nil{}}
    case l <> +rest:
      match vs:
        case Nil{}:
          under(l, decide.go(rest, Nil{}, room, stay))
        case v <> vr:
          match v:
            case Defer{}:
              under(l, decide.go(rest, vr, room, stay))
            case Again{}:
              spend(l, rest)
            case Yield{}:
              Dec{Hand{}, l <> rest}
            case Stack{n}:
              push(l, n, rest, room)
            case Leave{}:
              decide.go(rest, vr, room, stay)
            case Abort{}:
              Dec{Failed{}, l <> rest}
            case Lead{}:
              lead(stay, l, decide.go(rest, vr, room, stay))

# One decision of the stack s with room for cap layers: a push needs the
# whole stack to hold fewer than cap layers
def decide.as(+s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat, +stay: Bool) -> Dec:
  decide.go(s, vs, Nat.is_lt(List.length(&2, Layer, s), cap), stay)

# One decision of the stack when the loop goes on: a layer that leads
# leaves
def decide(+s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat) -> Dec:
  decide.as(s, vs, cap, False{})

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

# the stack s after a decision on vs that ends the loop: a layer that
# leads stays
def kept(+s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat) -> List<&2, Layer>:
  Dec.stack(decide.as(s, vs, cap, True{}))

# a continue with n steps left: with a step left the loop goes on with the
# stack t; with none it yields
def go.on(n: Nat, t: List<&2, Layer>, +s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat) -> Loop:
  match n:
    case 0n:
      Loop{0n, kept(s, vs, cap), Some{Hand{}}}
    case 1n+m:
      Loop{m, t, None{}}

# the loop after the decision d of the stack s on vs, with n steps left
def settle(d: Dec, +n: Nat, +s: List<&2, Layer>, vs: List<&2, Verdict>, +cap: Nat) -> Loop:
  match d:
    case Dec{o, t}:
      match o:
        case Cont{}:
          go.on(n, t, s, vs, cap)
        case Hand{}:
          Loop{n, kept(s, vs, cap), Some{Hand{}}}
        case Failed{}:
          Loop{n, kept(s, vs, cap), Some{Failed{}}}

# one loop step: the stack decides on the verdicts vs
def tick(+cap: Nat, l: Loop, vs: List<&2, Verdict>) -> Loop:
  match l:
    case Loop{n, +s, e}:
      match e:
        case None{}:
          +w = vs
          settle(decide(s, w, cap), n, s, w, cap)
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
