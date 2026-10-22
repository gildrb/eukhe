# ffi_tree: the stepper of the compiled Bend core for the session tree
# (crates/eukhe-durable/src/tree/journal.rs): its state is the core of
# bend/tree.bend (`M.St`: the live key map and the journal), kept in the
# Bend heap. Each step is one question to `M.core.step`; the reply is its
# answer. The codec is the wire format of bend/wire.bend:
#
#   open   List<Nat>: the halves of the key range, from the top   reply: empty
#   step   Ask                                                    reply: Ans
#   Ask    0, Rec (note) | 1, n: Nat (plan) | 2, n: Nat (snap)
#   Rec    0, Op (do) | 1, List<Op> (rewind)
#   Op     0, k: Nat, p: Nat, v: Nat (put) | 1, k: Nat (del)
#   Ans    0 (kept) | 1 (took) | 2, List<Nat> (cut) | 3, List<Eff>
#          (effects) | 4, List<Ent> (nodes)
#   Eff    0, k (start) | 1, k (stop) | 2, k (restore)
#   Ent    k: Nat, p: Nat, v: Nat
#
# A malformed input, or one with input left over, answers the wire's
# error form; a step keeps the state then, and a malformed open opens the
# refused state, which answers every step with the error form.
# LAWS.bend (S1, tree_ffi_*) pins the codec and the entry.

import Base
import ./wire.bend as W
import ./tree.bend as M

# Encoders
# --------

def put_op(o: M.Op, rest: String) -> String:
  match o:
    case M.Put{k, p, v}:
      W.put_nat(0n, W.put_nat(k, W.put_nat(p, W.put_nat(v, rest))))
    case M.Del{k}:
      W.put_nat(1n, W.put_nat(k, rest))

def put_rec(r: M.Rec, rest: String) -> String:
  match r:
    case M.Do{o}:
      W.put_nat(0n, put_op(o, rest))
    case M.Rewind{ops}:
      W.put_nat(1n, W.put_list(~M.Op, ~put_op, ops, rest))

# the request of a step (Rust writes it; the laws read it back)
def put_ask(q: M.Ask, rest: String) -> String:
  match q:
    case M.Note{r}:
      W.put_nat(0n, put_rec(r, rest))
    case M.Plan{n}:
      W.put_nat(1n, W.put_nat(n, rest))
    case M.Snap{n}:
      W.put_nat(2n, W.put_nat(n, rest))

def put_eff(e: M.Eff, rest: String) -> String:
  match e:
    case M.Start{k}:
      W.put_nat(0n, W.put_nat(k, rest))
    case M.Stop{k}:
      W.put_nat(1n, W.put_nat(k, rest))
    case M.Restore{k}:
      W.put_nat(2n, W.put_nat(k, rest))

def put_ent(e: M.Ent, rest: String) -> String:
  match e:
    case M.Ent{k, p, v}:
      W.put_nat(k, W.put_nat(p, W.put_nat(v, rest)))

# the reply of a step
def put_ans(a: M.Ans, rest: String) -> String:
  match a:
    case M.Kept{}:
      W.put_nat(0n, rest)
    case M.Took{}:
      W.put_nat(1n, rest)
    case M.Cut{ks}:
      W.put_nat(2n, W.put_list(~Nat, ~W.put_nat, ks, rest))
    case M.Effects{es}:
      W.put_nat(3n, W.put_list(~M.Eff, ~put_eff, es, rest))
    case M.Nodes{es}:
      W.put_nat(4n, W.put_list(~M.Ent, ~put_ent, es, rest))

# Decoders
# --------

def get_op.v(k: Nat, p: Nat, r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{v, s}:
      W.Got{M.Put{k, p, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.p(k: Nat, r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{p, s}:
      get_op.v(k, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_op.put(r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{k, s}:
      get_op.p(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_op.del(r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{k, s}:
      W.Got{M.Del{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.tag(n: Nat, s: String) -> W.Dec<M.Op>:
  match n:
    case 0n:
      get_op.put(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          get_op.del(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_op.go(r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{n, s}:
      get_op.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_op(s: String) -> W.Dec<M.Op>:
  get_op.go(W.get_nat(s))

def get_rec.do(r: W.Dec<M.Op>) -> W.Dec<M.Rec>:
  match r:
    case W.Got{o, s}:
      W.Got{M.Do{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_rec.rewind(r: W.Dec<List<&2, M.Op>>) -> W.Dec<M.Rec>:
  match r:
    case W.Got{ops, s}:
      W.Got{M.Rewind{ops}, s}
    case W.Bad{}:
      W.Bad{}

def get_rec.tag(n: Nat, s: String) -> W.Dec<M.Rec>:
  match n:
    case 0n:
      get_rec.do(get_op(s))
    case 1n+a:
      match a:
        case 0n:
          get_rec.rewind(W.get_list(~M.Op, ~get_op, s))
        case 1n+b:
          W.Bad{}

def get_rec.go(r: W.Dec<Nat>) -> W.Dec<M.Rec>:
  match r:
    case W.Got{n, s}:
      get_rec.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_rec(s: String) -> W.Dec<M.Rec>:
  get_rec.go(W.get_nat(s))

def get_ask.note(r: W.Dec<M.Rec>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{x, s}:
      W.Got{M.Note{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.plan(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Plan{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.snap(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Snap{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(n: Nat, s: String) -> W.Dec<M.Ask>:
  match n:
    case 0n:
      get_ask.note(get_rec(s))
    case 1n+a:
      match a:
        case 0n:
          get_ask.plan(W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              get_ask.snap(W.get_nat(s))
            case 1n+c:
              W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      get_ask.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the request of a step
def get_ask(s: String) -> W.Dec<M.Ask>:
  get_ask.go(W.get_nat(s))

# The stepper
# -----------

# the core of the session tree, or a refused open
type St is Data:
  Live{s: M.St}
  Shut{}

def open.end(done: Bool, hs: List<&2, Nat>) -> St & String:
  match done:
    case True{}:
      (Live{M.core.start(hs)}, "")
    case False{}:
      (Shut{}, W.err("tree: input left after the halves"))

def open.go(r: W.Dec<List<&2, Nat>>) -> St & String:
  match r:
    case W.Got{hs, s}:
      open.end(W.end(s), hs)
    case W.Bad{}:
      (Shut{}, W.err("tree: malformed halves"))

# open: an empty core whose key map splits its places at the halves of
# the input
def open(input: String) -> St & String:
  open.go(W.get_list(~Nat, ~W.get_nat, input))

def step.ans(r: M.St & M.Ans) -> St & String:
  (s, a) = r
  (Live{s}, put_ans(a, ""))

def step.end(done: Bool, s: M.St, q: M.Ask) -> St & String:
  match done:
    case True{}:
      step.ans(M.core.step(s, q))
    case False{}:
      (Live{s}, W.err("tree: input left after the ask"))

def step.ask(s: M.St, r: W.Dec<M.Ask>) -> St & String:
  match r:
    case W.Got{q, rest}:
      step.end(W.end(rest), s, q)
    case W.Bad{}:
      (Live{s}, W.err("tree: malformed ask"))

# step: one question to the core; the reply is its answer
def step(st: St, input: String) -> St & String:
  match st:
    case Live{s}:
      step.ask(s, get_ask(input))
    case Shut{}:
      (Shut{}, W.err("tree: the open was refused"))
