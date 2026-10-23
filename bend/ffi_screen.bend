# ffi_screen: the compiled core's entry for the interface model
# (bend/screen.bend): the transcript ledger, the pace, the vertical
# stack and the paint decision, called per frame by crates/eukhe-tui
# (`view/ledger.rs`, `pace.rs`, `view/stack.rs`, `inline_term.rs`). The
# wire format is bend/wire.bend (crates/eukhe-bend/WIRE.md).
#
# A request is one constructor:
#   0 Run{tx, events}           the events of a frame on the blocks after
#                               the committed prefix (law
#                               tx_committed_inert); answers the Tx
#   1 Pace{min, k, pace, n}     n characters arrive, then a frame (pace.run
#                               of [Chunk{n}, Frame]); answers the Pace
#   2 Stack{heights, y, rows}   vstack; answers the rects
#   3 Paint{checks}             the paint decision (resync of present) on
#                               the checks run so far, in order (at most
#                               three: the frame, its full redraw, its
#                               fresh redraw); answers a Step
# Tx = blocks (a List of Blk = id, state tag (0 active, 1 final, 2
# committed), len), next, width. Ev tags: 0 Open, 1 Grow{id, n}, 2 Fin{id},
# 3 Flush, 4 Resize{w}. Pace = recv, shown.
# Rect = y, h. Step: 0 (run the next check), 1 frame full (Put), 2 frame
# (Fresh) or 3 frame (Kept); a frame is the index of the attempt that
# built it (0 the frame, 1 its full redraw, 2 its fresh redraw). A
# malformed request (or input left over, or more than three checks)
# answers the error form, never a default.

import Base
import ./wire.bend as W
import ./screen.bend as Sc

type Req is Data:
  ReqRun{tx: Sc.Tx, es: List<&2, Sc.Ev>}
  ReqPace{min: Nat, k: Nat, p: Sc.Pace, n: Nat}
  ReqStack{hs: List<&2, Nat>, y: Nat, rows: Nat}
  ReqPaint{ks: List<&2, Bool>}

# Encoders
# --------

def put_st(s: Sc.St, rest: String) -> String:
  match s:
    case Sc.Active{}:
      W.put_nat(0n, rest)
    case Sc.Final{}:
      W.put_nat(1n, rest)
    case Sc.Comm{}:
      W.put_nat(2n, rest)

def put_blk(b: Sc.Blk, rest: String) -> String:
  match b:
    case Sc.Blk{i, s, l}:
      W.put_nat(i, put_st(s, W.put_nat(l, rest)))

def put_tx(t: Sc.Tx, rest: String) -> String:
  match t:
    case Sc.Tx{bs, n, w}:
      W.put_list(~Sc.Blk, ~put_blk, bs, W.put_nat(n, W.put_nat(w, rest)))

def put_ev(e: Sc.Ev, rest: String) -> String:
  match e:
    case Sc.Open{}:
      W.put_nat(0n, rest)
    case Sc.Grow{x, n}:
      W.put_nat(1n, W.put_nat(x, W.put_nat(n, rest)))
    case Sc.Fin{x}:
      W.put_nat(2n, W.put_nat(x, rest))
    case Sc.Flush{}:
      W.put_nat(3n, rest)
    case Sc.Resize{w}:
      W.put_nat(4n, W.put_nat(w, rest))

def put_pace(p: Sc.Pace, rest: String) -> String:
  match p:
    case Sc.Pace{r, s}:
      W.put_nat(r, W.put_nat(s, rest))

def put_rect(r: Sc.Rect, rest: String) -> String:
  match r:
    case Sc.Rect{y, h}:
      W.put_nat(y, W.put_nat(h, rest))

# the paint decision, or None while the next check must run
def put_step(m: Maybe<&2, Sc.Paint>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          W.put_nat(1n, W.put_nat(f, W.put_bool(full, rest)))
        case Sc.Fresh{f}:
          W.put_nat(2n, W.put_nat(f, rest))
        case Sc.Kept{f}:
          W.put_nat(3n, W.put_nat(f, rest))

# the encoding of a request (what Rust writes)
def put_req(q: Req, rest: String) -> String:
  match q:
    case ReqRun{t, es}:
      W.put_nat(0n, put_tx(t, W.put_list(~Sc.Ev, ~put_ev, es, rest)))
    case ReqPace{min, k, p, n}:
      W.put_nat(1n, W.put_nat(min, W.put_nat(k, put_pace(p, W.put_nat(n, rest)))))
    case ReqStack{hs, y, rows}:
      W.put_nat(2n, W.put_list(~Nat, ~W.put_nat, hs, W.put_nat(y, W.put_nat(rows, rest))))
    case ReqPaint{ks}:
      W.put_nat(3n, W.put_list(~Bool, ~W.put_bool, ks, rest))

# Decoders
# --------

def get_st.tag(n: Nat, s: String) -> W.Dec<Sc.St>:
  match n:
    case 0n:
      W.Got{Sc.Active{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Sc.Final{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Sc.Comm{}, s}
            case 1n+c:
              W.Bad{}

def get_st.of(r: W.Dec<Nat>) -> W.Dec<Sc.St>:
  match r:
    case W.Got{n, s}:
      get_st.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_st(s: String) -> W.Dec<Sc.St>:
  get_st.of(W.get_nat(s))

def get_blk.len(i: Nat, st: Sc.St, r: W.Dec<Nat>) -> W.Dec<Sc.Blk>:
  match r:
    case W.Got{l, s}:
      W.Got{Sc.Blk{i, st, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_blk.st(i: Nat, r: W.Dec<Sc.St>) -> W.Dec<Sc.Blk>:
  match r:
    case W.Got{st, s}:
      get_blk.len(i, st, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.id(r: W.Dec<Nat>) -> W.Dec<Sc.Blk>:
  match r:
    case W.Got{i, s}:
      get_blk.st(i, get_st(s))
    case W.Bad{}:
      W.Bad{}

def get_blk(s: String) -> W.Dec<Sc.Blk>:
  get_blk.id(W.get_nat(s))

def get_tx.w(bs: List<&2, Sc.Blk>, n: Nat, r: W.Dec<Nat>) -> W.Dec<Sc.Tx>:
  match r:
    case W.Got{w, s}:
      W.Got{Sc.Tx{bs, n, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_tx.n(bs: List<&2, Sc.Blk>, r: W.Dec<Nat>) -> W.Dec<Sc.Tx>:
  match r:
    case W.Got{n, s}:
      get_tx.w(bs, n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_tx.bs(r: W.Dec<List<&2, Sc.Blk>>) -> W.Dec<Sc.Tx>:
  match r:
    case W.Got{bs, s}:
      get_tx.n(bs, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_tx(s: String) -> W.Dec<Sc.Tx>:
  get_tx.bs(W.get_list(~Sc.Blk, ~get_blk, s))

def get_ev.one(r: W.Dec<Nat>) -> W.Dec<Sc.Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{Sc.Fin{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.w(r: W.Dec<Nat>) -> W.Dec<Sc.Ev>:
  match r:
    case W.Got{w, s}:
      W.Got{Sc.Resize{w}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.n(x: Nat, r: W.Dec<Nat>) -> W.Dec<Sc.Ev>:
  match r:
    case W.Got{n, s}:
      W.Got{Sc.Grow{x, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.x(r: W.Dec<Nat>) -> W.Dec<Sc.Ev>:
  match r:
    case W.Got{x, s}:
      get_ev.n(x, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<Sc.Ev>:
  match n:
    case 0n:
      W.Got{Sc.Open{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_ev.x(W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              get_ev.one(W.get_nat(s))
            case 1n+c:
              match c:
                case 0n:
                  W.Got{Sc.Flush{}, s}
                case 1n+d:
                  match d:
                    case 0n:
                      get_ev.w(W.get_nat(s))
                    case 1n+e:
                      W.Bad{}

def get_ev.of(r: W.Dec<Nat>) -> W.Dec<Sc.Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<Sc.Ev>:
  get_ev.of(W.get_nat(s))

def get_pace.s(r0: Nat, r: W.Dec<Nat>) -> W.Dec<Sc.Pace>:
  match r:
    case W.Got{sh, s}:
      W.Got{Sc.Pace{r0, sh}, s}
    case W.Bad{}:
      W.Bad{}

def get_pace.r(r: W.Dec<Nat>) -> W.Dec<Sc.Pace>:
  match r:
    case W.Got{rv, s}:
      get_pace.s(rv, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_pace(s: String) -> W.Dec<Sc.Pace>:
  get_pace.r(W.get_nat(s))

def get_run.es(t: Sc.Tx, r: W.Dec<List<&2, Sc.Ev>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{ReqRun{t, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_run(r: W.Dec<Sc.Tx>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_run.es(t, W.get_list(~Sc.Ev, ~get_ev, s))
    case W.Bad{}:
      W.Bad{}

def get_pacereq.n(min: Nat, k: Nat, p: Sc.Pace, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      W.Got{ReqPace{min, k, p, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_pacereq.p(min: Nat, k: Nat, r: W.Dec<Sc.Pace>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_pacereq.n(min, k, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_pacereq.k(min: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      get_pacereq.p(min, k, get_pace(s))
    case W.Bad{}:
      W.Bad{}

def get_pacereq(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{min, s}:
      get_pacereq.k(min, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_stack.rows(hs: List<&2, Nat>, y: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{rows, s}:
      W.Got{ReqStack{hs, y, rows}, s}
    case W.Bad{}:
      W.Bad{}

def get_stack.y(hs: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{y, s}:
      get_stack.rows(hs, y, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_stack(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{hs, s}:
      get_stack.y(hs, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_paint(r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{ks, s}:
      W.Got{ReqPaint{ks}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_run(get_tx(s))
    case 1n+a:
      match a:
        case 0n:
          get_pacereq(W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              get_stack(W.get_list(~Nat, ~W.get_nat, s))
            case 1n+c:
              match c:
                case 0n:
                  get_paint(W.get_list(~Bool, ~W.get_bool, s))
                case 1n+d:
                  W.Bad{}

def get_req.of(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the request at the head of s (what the entry reads)
def get_req(s: String) -> W.Dec<Req>:
  get_req.of(W.get_nat(s))

# The paint decision
# ------------------

# The model's paint (resync of present) with the frames as the indexes of
# the attempts that built them: 0 the frame, 1 its full redraw, 2 its
# fresh redraw. Rust runs a check only when the model's paint still
# depends on it: the decision on the checks run so far is the paint when
# every result of the checks not yet run gives that same paint, else None
# (run the next check).
def paint.of(a: Bool, b: Bool, c: Bool) -> Sc.Paint:
  Sc.resync(Sc.present(0n, 1n, a, b), 2n, c)

def paint.same(p: Sc.Paint, q: Sc.Paint) -> Bool:
  match p q:
    case Sc.Put{f, x} Sc.Put{g, y}:
      Bool.and(Nat.is_eq(f, g), Bool.not(Bool.xor(x, y)))
    case Sc.Put{f, x} Sc.Fresh{g}:
      False{}
    case Sc.Put{f, x} Sc.Kept{g}:
      False{}
    case Sc.Fresh{f} Sc.Put{g, y}:
      False{}
    case Sc.Fresh{f} Sc.Fresh{g}:
      Nat.is_eq(f, g)
    case Sc.Fresh{f} Sc.Kept{g}:
      False{}
    case Sc.Kept{f} Sc.Put{g, y}:
      False{}
    case Sc.Kept{f} Sc.Fresh{g}:
      False{}
    case Sc.Kept{f} Sc.Kept{g}:
      Nat.is_eq(f, g)

def paint.keep(same: Bool, p: Sc.Paint) -> Maybe<&2, Sc.Paint>:
  match same:
    case True{}:
      Some{p}
    case False{}:
      None{}

# the paint both halves decide, when they decide the same one
def paint.both(m: Maybe<&2, Sc.Paint>, n: Maybe<&2, Sc.Paint>) -> Maybe<&2, Sc.Paint>:
  match m n:
    case Some{+p} Some{q}:
      paint.keep(paint.same(p, q), p)
    case Some{p} None{}:
      None{}
    case None{} Some{q}:
      None{}
    case None{} None{}:
      None{}

def paint.d3(a: Bool, b: Bool, c: Bool) -> Maybe<&2, Sc.Paint>:
  Some{paint.of(a, b, c)}

def paint.d2(+a: Bool, +b: Bool) -> Maybe<&2, Sc.Paint>:
  paint.both(paint.d3(a, b, False{}), paint.d3(a, b, True{}))

def paint.d1(+a: Bool) -> Maybe<&2, Sc.Paint>:
  paint.both(paint.d2(a, False{}), paint.d2(a, True{}))

def paint.d0() -> Maybe<&2, Sc.Paint>:
  paint.both(paint.d1(False{}), paint.d1(True{}))

# the decision on the checks run so far (at most three; more: None)
def paint.decide(ks: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match ks:
    case Nil{}:
      paint.d0()
    case Con{a, r1}:
      match r1:
        case Nil{}:
          paint.d1(a)
        case Con{b, r2}:
          match r2:
            case Nil{}:
              paint.d2(a, b)
            case Con{c, r3}:
              match r3:
                case Nil{}:
                  paint.d3(a, b, c)
                case Con{d, r4}:
                  None{}

def paint.reply.fit(fits: Bool, ks: List<&2, Bool>) -> String:
  match fits:
    case True{}:
      put_step(paint.decide(ks), SNil{})
    case False{}:
      W.err("screen: more than three checks")

# the reply to the checks run so far: more than three is an error
def paint.reply(+ks: List<&2, Bool>) -> String:
  paint.reply.fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks)

# The entry
# ---------

# the model's answer to a request, encoded
def answer(q: Req) -> String:
  match q:
    case ReqRun{t, es}:
      put_tx(Sc.run(es, t), SNil{})
    case ReqPace{min, k, p, n}:
      put_pace(Sc.pace.run([Sc.Chunk{n}, Sc.Frame{}], min, k, p), SNil{})
    case ReqStack{hs, y, rows}:
      W.put_list(~Sc.Rect, ~put_rect, Sc.vstack(hs, y, rows), SNil{})
    case ReqPaint{ks}:
      paint.reply(ks)

def ffi.whole(q: Req, whole: Bool) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      W.err("screen: input left over")

def ffi.of(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.whole(q, W.end(s))
    case W.Bad{}:
      W.err("screen: malformed request")

def ffi(input: String) -> String:
  ffi.of(get_req(input))
