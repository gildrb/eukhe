# ffi_bound: the entry of the compiled Bend core for the bounder of a
# tool's output (bend/bound.bend; Rust: crates/eukhe-durable/src/harness/
# output.rs, tool/result.rs). Every request and every reply is one list
# of Nats of the wire (bend/wire.bend: its count, then its items); a Bool
# is 0 (false) or 1 (true). A cap is [bytes, lines, tail]; a body (the
# text Rust stores or bounds) is [open, head, tail, margin, line ...]: its
# Bool and its three cuts (bend/bound.bend `Body`), then its lines' bytes.
#
# The calls (`ffi`):
#   slice   [0, cap ..., body ...]       the window of a whole text
#     reply [from, to, bytes, lines]     where it lies; what it drops
#   notice  [1, tail, dropped, still]    the truncation notice
#     reply [] | [at]                    none | 0 at the end, 1 at the start
#
# The stepper of one output (`open`, `step`):
#   open    [cap ...]                    a new output under the cap
#     reply [skips]                      1: it takes the output a shell
#                                        left out (a tail), 0: it never does
#   out     [0, bytes, newlines, open]   a text of the output comes
#     reply [act]                        0 drop it, 1 store it, 2 store it
#                                        and then send the stored text
#   skip    [1, bytes, newlines, open]   a shell left out output
#     reply [clear]                      1: clear the stored text
#   look    [2, body ...]                the stored text
#     reply [from, to, bytes, lines, cut]  where the window lies in it;
#                                        the bytes and lines the output
#                                        dropped; where the stored text
#                                        now starts
#
# A malformed input (no list, input left over, a list of another shape)
# answers the wire's error form; a step keeps the state then, and a
# malformed open opens the refused state, which answers every step with
# the error form. laws/bound.bend pins the entry.

import Base
import ./wire.bend as W
import ./bound.bend as M

# Values as Nats
# --------------

def bitn(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def bit(n: Nat) -> Maybe<&2, Bool>:
  match n:
    case 0n:
      Some{False{}}
    case 1n:
      Some{True{}}
    case 2n+x:
      None{}

def act.n(a: M.Act) -> Nat:
  match a:
    case M.Drop{}:
      0n
    case M.Store{}:
      1n
    case M.Trim{}:
      2n

def at.n(a: M.At) -> Nat:
  match a:
    case M.AtEnd{}:
      0n
    case M.AtStart{}:
      1n

def span.nats(s: M.Span, rest: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case M.Span{f, t}:
      f <> t <> rest

def slice.nats(s: M.Slice) -> List<&2, Nat>:
  match s:
    case M.Slice{sp, b, l}:
      span.nats(sp, [b, l])

def seen.nats(s: M.Seen) -> List<&2, Nat>:
  match s:
    case M.Seen{sp, b, l, c}:
      span.nats(sp, [b, l, c])

def notice.nats(m: Maybe<&2, M.At>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{a}:
      [at.n(a)]

# Nats as values
# --------------

def cap.of(+b: Nat, +l: Nat, t: Maybe<&2, Bool>) -> Maybe<&2, M.Cap>:
  match t:
    case None{}:
      None{}
    case Some{x}:
      Some{M.Cap{b, l, x}}

def body.of(o: Maybe<&2, Bool>, +h: Nat, +t: Nat, +m: Nat, xs: List<&2, Nat>) -> Maybe<&2, M.Body>:
  match o:
    case None{}:
      None{}
    case Some{x}:
      Some{M.Body{xs, x, h, t, m}}

# the body a list spells: [open, head, tail, margin, line ...]
def body(xs: List<&2, Nat>) -> Maybe<&2, M.Body>:
  match xs:
    case Nil{}:
      None{}
    case o <> a:
      match a:
        case Nil{}:
          None{}
        case h <> b:
          match b:
            case Nil{}:
              None{}
            case t <> c:
              match c:
                case Nil{}:
                  None{}
                case m <> ls:
                  body.of(bit(o), h, t, m, ls)

# the cap a list starts with ([bytes, lines, tail]), and the rest
type CapAnd is Data:
  CapAnd{c: M.Cap, rest: List<&2, Nat>}

def cap.and(m: Maybe<&2, M.Cap>, rest: List<&2, Nat>) -> Maybe<&2, CapAnd>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{CapAnd{c, rest}}

def cap.lead(xs: List<&2, Nat>) -> Maybe<&2, CapAnd>:
  match xs:
    case Nil{}:
      None{}
    case b <> a:
      match a:
        case Nil{}:
          None{}
        case l <> c:
          match c:
            case Nil{}:
              None{}
            case t <> rest:
              cap.and(cap.of(b, l, bit(t)), rest)

# The calls
# ---------

type Req is Data:
  SliceQ{c: M.Cap, x: M.Body}
  NoticeQ{tail: Bool, dropped: Nat, still: Bool}

def req.slice.body(c: M.Cap, m: Maybe<&2, M.Body>) -> Maybe<&2, Req>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{SliceQ{c, x}}

def req.slice(m: Maybe<&2, CapAnd>) -> Maybe<&2, Req>:
  match m:
    case None{}:
      None{}
    case Some{ca}:
      match ca:
        case CapAnd{c, rest}:
          req.slice.body(c, body(rest))

def req.notice.of(t: Maybe<&2, Bool>, +d: Nat, s: Maybe<&2, Bool>) -> Maybe<&2, Req>:
  match t:
    case None{}:
      None{}
    case Some{a}:
      match s:
        case None{}:
          None{}
        case Some{b}:
          Some{NoticeQ{a, d, b}}

def req.notice(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case t <> a:
      match a:
        case Nil{}:
          None{}
        case d <> b:
          match b:
            case Nil{}:
              None{}
            case s <> c:
              match c:
                case Nil{}:
                  req.notice.of(bit(t), d, bit(s))
                case x <> y:
                  None{}

# the request a list spells
def req(xs: List<&2, Nat>) -> Maybe<&2, Req>:
  match xs:
    case Nil{}:
      None{}
    case tag <> t:
      match tag:
        case 0n:
          req.slice(cap.lead(t))
        case 1n:
          req.notice(t)
        case 2n+x:
          None{}

# the answer of a call, as its list
def answer(q: Req) -> List<&2, Nat>:
  match q:
    case SliceQ{c, x}:
      slice.nats(M.slice(c, x))
    case NoticeQ{t, d, s}:
      notice.nats(M.notice(t, d, s))

def reply(xs: List<&2, Nat>) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, "")

def ffi.ask(q: Maybe<&2, Req>) -> String:
  match q:
    case None{}:
      W.err("bound: malformed request")
    case Some{r}:
      reply(answer(r))

def ffi.end(done: Bool, xs: List<&2, Nat>) -> String:
  match done:
    case True{}:
      ffi.ask(req(xs))
    case False{}:
      W.err("bound: malformed request")

def ffi.got(r: W.Dec<List<&2, Nat>>) -> String:
  match r:
    case W.Got{xs, rest}:
      ffi.end(W.end(rest), xs)
    case W.Bad{}:
      W.err("bound: malformed request")

# ffi: one call (the window of a whole text, a notice)
def ffi(input: String) -> String:
  ffi.got(W.get_list(~Nat, ~W.get_nat, input))

# The stream
# ----------

# an output under a cap, or a refused open
type St is Data:
  Run{s: M.St}
  Shut{}

# an event of the output
type Ev is Data:
  OutE{n: Nat, k: Nat, o: Bool}
  SkipE{n: Nat, k: Nat, o: Bool}
  LookE{x: M.Body}

def ev.counts(o: Maybe<&2, Bool>, tag: Nat, +n: Nat, +k: Nat) -> Maybe<&2, Ev>:
  match o:
    case None{}:
      None{}
    case Some{b}:
      match tag:
        case 0n:
          Some{OutE{n, k, b}}
        case 1n+x:
          Some{SkipE{n, k, b}}

# [n, k, open] of a text or a skip
def ev.three(tag: Nat, xs: List<&2, Nat>) -> Maybe<&2, Ev>:
  match xs:
    case Nil{}:
      None{}
    case n <> a:
      match a:
        case Nil{}:
          None{}
        case k <> b:
          match b:
            case Nil{}:
              None{}
            case o <> c:
              match c:
                case Nil{}:
                  ev.counts(bit(o), tag, n, k)
                case x <> y:
                  None{}

def ev.look(m: Maybe<&2, M.Body>) -> Maybe<&2, Ev>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{LookE{x}}

# the event a list spells
def ev(xs: List<&2, Nat>) -> Maybe<&2, Ev>:
  match xs:
    case Nil{}:
      None{}
    case tag <> t:
      match tag:
        case 0n:
          ev.three(0n, t)
        case 1n:
          ev.three(1n, t)
        case 2n:
          ev.look(body(t))
        case 3n+x:
          None{}

def open.of(m: Maybe<&2, CapAnd>) -> St & String:
  match m:
    case None{}:
      (Shut{}, W.err("bound: malformed open"))
    case Some{ca}:
      match ca:
        case CapAnd{+c, rest}:
          match rest:
            case Nil{}:
              (Run{M.start(c)}, reply([bitn(M.Cap.tail(c))]))
            case x <> y:
              (Shut{}, W.err("bound: malformed open"))

def open.end(done: Bool, xs: List<&2, Nat>) -> St & String:
  match done:
    case True{}:
      open.of(cap.lead(xs))
    case False{}:
      (Shut{}, W.err("bound: malformed open"))

def open.got(r: W.Dec<List<&2, Nat>>) -> St & String:
  match r:
    case W.Got{xs, rest}:
      open.end(W.end(rest), xs)
    case W.Bad{}:
      (Shut{}, W.err("bound: malformed open"))

# open: a new output under the cap of the input, nothing come yet
def open(input: String) -> St & String:
  open.got(W.get_list(~Nat, ~W.get_nat, input))

def step.out(r: M.St & M.Act) -> St & String:
  match r:
    case (s, a):
      (Run{s}, reply([act.n(a)]))

def step.skip(r: M.St & Bool) -> St & String:
  match r:
    case (s, b):
      (Run{s}, reply([bitn(b)]))

def step.look(r: M.St & M.Seen) -> St & String:
  match r:
    case (s, v):
      (Run{s}, reply(seen.nats(v)))

def step.ev(st: St, m: Maybe<&2, Ev>) -> St & String:
  match st:
    case Run{s}:
      match m:
        case None{}:
          (Run{s}, W.err("bound: malformed event"))
        case Some{e}:
          match e:
            case OutE{n, k, o}:
              step.out(M.out(s, n, k, o))
            case SkipE{n, k, o}:
              step.skip(M.skip(s, n, k, o))
            case LookE{x}:
              step.look(M.look(s, x))
    case Shut{}:
      (Shut{}, W.err("bound: the open was refused"))

def step.end(st: St, done: Bool, xs: List<&2, Nat>) -> St & String:
  match done:
    case True{}:
      step.ev(st, ev(xs))
    case False{}:
      step.ev(st, None{})

def step.got(st: St, r: W.Dec<List<&2, Nat>>) -> St & String:
  match r:
    case W.Got{xs, rest}:
      step.end(st, W.end(rest), xs)
    case W.Bad{}:
      step.ev(st, None{})

# step: one event of the output; the reply is the decision on it
def step(st: St, input: String) -> St & String:
  step.got(st, W.get_list(~Nat, ~W.get_nat, input))
