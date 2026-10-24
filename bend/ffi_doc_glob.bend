# ffi_doc_glob: the entry of the compiled Bend core for glob
# (crates/eukhe-docs/src/glob.rs), a stepper over the rule of
# bend/doc_glob.bend: Rust walks, reads times and spells paths; the
# stepper ranks, keeps and pages, one matched path at a time. Requests and
# replies are values of the wire (bend/wire.bend); a Maybe<Nat> is 0
# (none) or 1 then the value.
#
#   open  s lim             skip s, limit lim (a Maybe<Nat>)
#     reply empty
#   met   0 m               a matched path, changed at m ms
#     reply T | F           T: send it whole (add); F: the core cannot keep
#                           it: Rust does not spell it
#   add   1 m p             the path p, changed at m
#     reply empty
#   page  2                 the page of the paths met so far
#     reply next past [m p ...]   the continuation (Maybe<Nat>), the count
#                           of paths when the skip is past the end
#                           (Maybe<Nat>), the page's paths with their times
#
# A malformed input (not exactly one of these spellings) answers the
# wire's error form; a step keeps the state then, and a malformed open
# opens the refused state, which answers every step with the error form.
# laws/doc_glob.bend pins the entry.

import Base
import ./wire.bend as W
import ./doc_glob.bend as M

# a glob: the page (skip s, k paths), the paths kept at most c, len paths
# kept, the oldest time kept low, the kept paths ranked; or a refused open
type St is Data:
  Gl{s: Nat, k: Nat, c: Nat, len: Nat, low: Nat, xs: List<&2, M.It>}
  Shut{}

# an event: a path's time; a path whole; the page
type Ev is Data:
  Met{m: Nat}
  Add{m: Nat, p: String}
  Show{}

# Open
# ----

def lim.end(e: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Maybe<&2, Nat>>:
  match e:
    case True{}:
      Some{m}
    case False{}:
      None{}

def lim.one(d: W.Dec<Nat>) -> Maybe<&2, Maybe<&2, Nat>>:
  match d:
    case W.Got{l, r}:
      lim.end(W.end(r), Some{l})
    case W.Bad{}:
      None{}

# the limit, the whole rest of the open: 0 (none) or 1 then the limit
def lim.tag(d: W.Dec<Nat>) -> Maybe<&2, Maybe<&2, Nat>>:
  match d:
    case W.Got{t, r}:
      match t:
        case 0n:
          lim.end(W.end(r), None{})
        case 1n:
          lim.one(W.get_nat(r))
        case 2n+x:
          None{}
    case W.Bad{}:
      None{}

def open.lim(+s: Nat, m: Maybe<&2, Maybe<&2, Nat>>) -> St & String:
  match m:
    case None{}:
      (Shut{}, W.err("doc_glob: malformed open"))
    case Some{lim}:
      +k = M.size(lim)
      (Gl{s, k, M.keep(s, k), 0n, 0n, Nil{}}, "")

def open.got(d: W.Dec<Nat>) -> St & String:
  match d:
    case W.Got{s, r}:
      open.lim(s, lim.tag(W.get_nat(r)))
    case W.Bad{}:
      (Shut{}, W.err("doc_glob: malformed open"))

# open: a glob of the page of the input, no path met
def open(input: String) -> St & String:
  open.got(W.get_nat(input))

# Events
# ------

def ev.end(e: Bool, v: Ev) -> Maybe<&2, Ev>:
  match e:
    case True{}:
      Some{v}
    case False{}:
      None{}

def ev.met(d: W.Dec<Nat>) -> Maybe<&2, Ev>:
  match d:
    case W.Got{m, r}:
      ev.end(W.end(r), Met{m})
    case W.Bad{}:
      None{}

def ev.path(m: Nat, d: W.Dec<String>) -> Maybe<&2, Ev>:
  match d:
    case W.Got{p, r}:
      ev.end(W.end(r), Add{m, p})
    case W.Bad{}:
      None{}

def ev.add(d: W.Dec<Nat>) -> Maybe<&2, Ev>:
  match d:
    case W.Got{m, r}:
      ev.path(m, W.get_str(r))
    case W.Bad{}:
      None{}

# the event the whole input spells
def ev(d: W.Dec<Nat>) -> Maybe<&2, Ev>:
  match d:
    case W.Got{t, r}:
      match t:
        case 0n:
          ev.met(W.get_nat(r))
        case 1n:
          ev.add(W.get_nat(r))
        case 2n:
          ev.end(W.end(r), Show{})
        case 3n+x:
          None{}
    case W.Bad{}:
      None{}

# Steps
# -----

def step.fin(+s: Nat, +k: Nat, +c: Nat, f: M.Fin) -> St & String:
  match f:
    case M.Fin{xs, len, low}:
      (Gl{s, k, c, len, low, xs}, "")

def put_opt(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{v}:
      W.put_nat(1n, W.put_nat(v, rest))

def put_it(x: M.It, rest: String) -> String:
  match x:
    case M.It{m, p, h}:
      W.put_nat(m, W.put_str(p, rest))

# the page of the kept paths: the continuation, the count when the skip
# is past the end, the page's paths
def say.page(xs: List<&2, M.It>, +s: Nat, +k: Nat, +len: Nat) -> String:
  put_opt(M.next(s, k, len), put_opt(M.past(s, len), W.put_list(~M.It, ~put_it, M.page(xs, s, k), "")))

def step.ev(st: St, e: Maybe<&2, Ev>) -> St & String:
  match st:
    case Gl{+s, +k, +c, +len, +low, +xs}:
      match e:
        case None{}:
          (Gl{s, k, c, len, low, xs}, W.err("doc_glob: malformed event"))
        case Some{v}:
          match v:
            case Met{m}:
              (Gl{s, k, c, len, low, xs}, W.put_bool(Bool.not(Bool.and(Nat.is_le(c, len), Nat.is_lt(m, low))), ""))
            case Add{m, p}:
              step.fin(s, k, c, M.fin(M.ins(M.it(m, p), xs), c))
            case Show{}:
              (Gl{s, k, c, len, low, xs}, say.page(xs, s, k, len))
    case Shut{}:
      (Shut{}, W.err("doc_glob: the open was refused"))

# step: one event of the walk; the reply is the decision on it
def step(st: St, input: String) -> St & String:
  step.ev(st, ev(W.get_nat(input)))
