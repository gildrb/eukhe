# eukhe: the laws of area screen, section requirement: the entry bend/ffi_screen.bend on every input, from the
# requirement

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr

# ---- screen: the entry from the requirement ----

# The spec of the whole entry, written from the requirement (S8, the rules
# of the interface in the header of bend/screen.bend and the laws above)
# and the wire's primitives only: no function of bend/screen.bend or
# bend/ffi_screen.bend (their types only), but Sc.reveal through the plain
# formula pace_reveal_formula pins.

# block i (state s, length l) after the change g: Some{n} grows an active
# block by n characters, up to 2^32 - 1 (a length already past it stays),
# None makes it final; a final or committed block stays as it is
def sc_sp_change(g: Maybe<&2, Nat>, i: Nat, s: Sc.St, +l: Nat) -> Sc.Blk:
  match g:
    case None{}:
      match s:
        case Sc.Active{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Final{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Comm{}:
          Sc.Blk{i, Sc.Comm{}, l}
    case Some{n}:
      match s:
        case Sc.Active{}:
          Sc.Blk{i, Sc.Active{}, Nat.max(l, Nat.min(Nat.add(l, n), 4294967295n))}
        case Sc.Final{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Comm{}:
          Sc.Blk{i, Sc.Comm{}, l}

# the block, changed by g when its id is the event's (hit)
def sc_sp_edit.at(hit: Bool, g: Maybe<&2, Nat>, i: Nat, s: Sc.St, l: Nat) -> Sc.Blk:
  match hit:
    case True{}:
      sc_sp_change(g, i, s, l)
    case False{}:
      Sc.Blk{i, s, l}

# every block of bs with id x changed by g, the others as they are
def sc_sp_edit(bs: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>) -> List<&2, Sc.Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Sc.Blk{+i, s, l}:
          sc_sp_edit.at(Nat.is_eq(i, x), g, i, s, l) <> sc_sp_edit(rest, x, g)

# a flush: the final blocks from the start are committed, up to the first
# active block (it and every block after it stay)
def sc_sp_flush(bs: List<&2, Sc.Blk>) -> List<&2, Sc.Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              Sc.Blk{i, Sc.Comm{}, l} <> sc_sp_flush(rest)
            case Sc.Final{}:
              Sc.Blk{i, Sc.Comm{}, l} <> sc_sp_flush(rest)
            case Sc.Active{}:
              Sc.Blk{i, Sc.Active{}, l} <> rest

# one event on the transcript: Open adds an active empty block with the
# next id (then the next id is one more), Grow and Fin change the blocks
# with their id, Flush commits, Resize sets the width
def sc_sp_step(t: Sc.Tx, e: Sc.Ev) -> Sc.Tx:
  match t:
    case Sc.Tx{bs, +n, w}:
      match e:
        case Sc.Open{}:
          Sc.Tx{List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}]), 1n+n, w}
        case Sc.Grow{x, k}:
          Sc.Tx{sc_sp_edit(bs, x, Some{k}), n, w}
        case Sc.Fin{x}:
          Sc.Tx{sc_sp_edit(bs, x, None{}), n, w}
        case Sc.Flush{}:
          Sc.Tx{sc_sp_flush(bs), n, w}
        case Sc.Resize{v}:
          Sc.Tx{bs, n, v}

# the events es, in order, on the transcript t
def sc_sp_run(es: List<&2, Sc.Ev>, t: Sc.Tx) -> Sc.Tx:
  match es:
    case Nil{}:
      t
    case e <> rest:
      sc_sp_run(rest, sc_sp_step(t, e))

# the characters a frame adds with backlog b (pace_reveal_formula)
def sc_sp_reveal(+min: Nat, +k: Nat, +b: Nat) -> Nat:
  Nat.min(b, Nat.max(min, Nat.div(b, 1n+k)))

# n characters arrive on the pace (r received, s shown), then a frame
def sc_sp_pace(+min: Nat, +k: Nat, +r: Nat, +s: Nat, +n: Nat) -> String:
  +r2 = Nat.add(r, n)
  Wr.put_nat(r2, Wr.put_nat(Nat.add(s, sc_sp_reveal(min, k, Nat.sub(r2, s))), ""))

# children of heights hs from row y in a viewport of `rows` rows: each at
# its row, its visible height cut at the viewport's bottom
def sc_sp_stack(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> List<&2, Sc.Rect>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Sc.Rect{y, Nat.min(h, Nat.sub(rows, y))} <> sc_sp_stack(rest, Nat.add(y, h), rows)

# the paint m when at most n more checks than the one it reads ran (r the
# checks after it), else none (more than three checks)
def sc_sp_short(r: List<&2, Bool>, n: Nat, m: Maybe<&2, Sc.Paint>) -> Maybe<&2, Sc.Paint>:
  match r:
    case Nil{}:
      m
    case x <> rest:
      match n:
        case 0n:
          None{}
        case 1n+k:
          sc_sp_short(rest, k, m)

# the third check c passed (the fresh redraw is drawn) or failed (the
# first frame is kept); r the checks after it
def sc_sp_d3(c: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match c:
    case True{}:
      sc_sp_short(r, 0n, Some{Sc.Fresh{2n}})
    case False{}:
      sc_sp_short(r, 0n, Some{Sc.Kept{0n}})

# the second check b passed (the full redraw is drawn), or the third
# decides
def sc_sp_d2(b: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match b:
    case True{}:
      sc_sp_short(r, 1n, Some{Sc.Put{1n, True{}}})
    case False{}:
      match r:
        case Nil{}:
          None{}
        case c <> rest:
          sc_sp_d3(c, rest)

# the first check a passed (the frame is drawn), or the second decides
def sc_sp_d1(a: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match a:
    case True{}:
      sc_sp_short(r, 2n, Some{Sc.Put{0n, False{}}})
    case False{}:
      match r:
        case Nil{}:
          None{}
        case b <> rest:
          sc_sp_d2(b, rest)

# the paint on the checks run so far, in order (the frame, its full
# redraw, its fresh redraw): the first passing check's frame; all three
# failed: kept, the first frame; while every check so far failed and
# fewer than three ran (or more than three ran): none yet
def sc_sp_decide(ks: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match ks:
    case Nil{}:
      None{}
    case a <> rest:
      sc_sp_d1(a, rest)

def sc_sp_put_st(s: Sc.St, rest: String) -> String:
  match s:
    case Sc.Active{}:
      Wr.put_nat(0n, rest)
    case Sc.Final{}:
      Wr.put_nat(1n, rest)
    case Sc.Comm{}:
      Wr.put_nat(2n, rest)

# a block: its id, its state's tag, its length
def sc_sp_put_blk(b: Sc.Blk, rest: String) -> String:
  match b:
    case Sc.Blk{i, s, l}:
      Wr.put_nat(i, sc_sp_put_st(s, Wr.put_nat(l, rest)))

# a transcript: its blocks, the next id, the width
def sc_sp_put_tx(t: Sc.Tx) -> String:
  match t:
    case Sc.Tx{bs, n, w}:
      Wr.put_list(~Sc.Blk, ~sc_sp_put_blk, bs, Wr.put_nat(n, Wr.put_nat(w, "")))

def sc_sp_put_rect(r: Sc.Rect, rest: String) -> String:
  match r:
    case Sc.Rect{y, h}:
      Wr.put_nat(y, Wr.put_nat(h, rest))

# a step of the paint: 0 (run the next check), 1 frame full, 2 frame, 3
# frame
def sc_sp_put_step(m: Maybe<&2, Sc.Paint>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          Wr.put_nat(1n, Wr.put_nat(f, Wr.put_bool(full, "")))
        case Sc.Fresh{f}:
          Wr.put_nat(2n, Wr.put_nat(f, ""))
        case Sc.Kept{f}:
          Wr.put_nat(3n, Wr.put_nat(f, ""))

def sc_sp_paint.fit(fits: Bool, ks: List<&2, Bool>) -> String:
  match fits:
    case True{}:
      sc_sp_put_step(sc_sp_decide(ks))
    case False{}:
      Wr.err("screen: more than three checks")

# the reply to the checks run so far: more than three is an error
def sc_sp_paint(+ks: List<&2, Bool>) -> String:
  sc_sp_paint.fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks)

# the spec's answer to a request
def sc_sp_answer(q: FSc.Req) -> String:
  match q:
    case FSc.ReqRun{t, es}:
      sc_sp_put_tx(sc_sp_run(es, t))
    case FSc.ReqPace{min, k, p, n}:
      match p:
        case Sc.Pace{r, s}:
          sc_sp_pace(min, k, r, s, n)
    case FSc.ReqStack{hs, y, rows}:
      Wr.put_list(~Sc.Rect, ~sc_sp_put_rect, sc_sp_stack(hs, y, rows), "")
    case FSc.ReqPaint{ks}:
      sc_sp_paint(ks)

# The reader
# ----------

def sc_sp_st.tag(n: Nat, s: String) -> Wr.Dec<Sc.St>:
  match n:
    case 0n:
      Wr.Got{Sc.Active{}, s}
    case 1n:
      Wr.Got{Sc.Final{}, s}
    case 2n:
      Wr.Got{Sc.Comm{}, s}
    case 3n+p:
      Wr.Bad{}

def sc_sp_st.of(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.St>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_st.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.len(i: Nat, st: Sc.St, r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{Sc.Blk{i, st, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.st(i: Nat, r: Wr.Dec<Sc.St>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{st, s}:
      sc_sp_blk.len(i, st, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.id(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{i, s}:
      sc_sp_blk.st(i, sc_sp_st.of(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a block: its id, its state's tag (0 active, 1 final, 2 committed), its
# length
def sc_sp_blk(s: String) -> Wr.Dec<Sc.Blk>:
  sc_sp_blk.id(Wr.get_nat(s))

def sc_sp_ev.one(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Sc.Fin{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.w(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{Sc.Resize{w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.n(x: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Sc.Grow{x, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.x(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{x, s}:
      sc_sp_ev.n(x, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.tag(n: Nat, s: String) -> Wr.Dec<Sc.Ev>:
  match n:
    case 0n:
      Wr.Got{Sc.Open{}, s}
    case 1n:
      sc_sp_ev.x(Wr.get_nat(s))
    case 2n:
      sc_sp_ev.one(Wr.get_nat(s))
    case 3n:
      Wr.Got{Sc.Flush{}, s}
    case 4n:
      sc_sp_ev.w(Wr.get_nat(s))
    case 5n+p:
      Wr.Bad{}

def sc_sp_ev.of(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_ev.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# an event: its tag (0 Open, 1 Grow, 2 Fin, 3 Flush, 4 Resize), then its
# fields
def sc_sp_ev(s: String) -> Wr.Dec<Sc.Ev>:
  sc_sp_ev.of(Wr.get_nat(s))

def sc_sp_run.es(t: Sc.Tx, r: Wr.Dec<List<&2, Sc.Ev>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{FSc.ReqRun{t, es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_run.w(bs: List<&2, Sc.Blk>, n: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{w, s}:
      sc_sp_run.es(Sc.Tx{bs, n, w}, Wr.get_list(~Sc.Ev, ~sc_sp_ev, s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_run.n(bs: List<&2, Sc.Blk>, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_run.w(bs, n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a run: the blocks, the next id, the width, then the events
def sc_sp_run.bs(r: Wr.Dec<List<&2, Sc.Blk>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{bs, s}:
      sc_sp_run.n(bs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.n(min: Nat, k: Nat, rv: Nat, sh: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{FSc.ReqPace{min, k, Sc.Pace{rv, sh}, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.sh(min: Nat, k: Nat, rv: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{sh, s}:
      sc_sp_pacereq.n(min, k, rv, sh, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.rv(min: Nat, k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{rv, s}:
      sc_sp_pacereq.sh(min, k, rv, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.k(min: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{k, s}:
      sc_sp_pacereq.rv(min, k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a pace: the minimum, the lag, received, shown, then the characters
# that arrive
def sc_sp_pacereq(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{min, s}:
      sc_sp_pacereq.k(min, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_stack.rows(hs: List<&2, Nat>, y: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{rows, s}:
      Wr.Got{FSc.ReqStack{hs, y, rows}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_stack.y(hs: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{y, s}:
      sc_sp_stack.rows(hs, y, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a stack: the heights, the start row, the rows
def sc_sp_stack.hs(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{hs, s}:
      sc_sp_stack.y(hs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a paint: the checks run so far
def sc_sp_paintreq(r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{ks, s}:
      Wr.Got{FSc.ReqPaint{ks}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_req.tag(n: Nat, s: String) -> Wr.Dec<FSc.Req>:
  match n:
    case 0n:
      sc_sp_run.bs(Wr.get_list(~Sc.Blk, ~sc_sp_blk, s))
    case 1n:
      sc_sp_pacereq(Wr.get_nat(s))
    case 2n:
      sc_sp_stack.hs(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n:
      sc_sp_paintreq(Wr.get_list(~Bool, ~Wr.get_bool, s))
    case 4n+p:
      Wr.Bad{}

def sc_sp_req.of(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_req.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with: its tag (0 run, 1 pace, 2 stack, 3 paint),
# then its fields; and what follows
def sc_sp_req(s: String) -> Wr.Dec<FSc.Req>:
  sc_sp_req.of(Wr.get_nat(s))

def sc_sp.whole(q: FSc.Req, whole: Bool) -> String:
  match whole:
    case True{}:
      sc_sp_answer(q)
    case False{}:
      Wr.err("screen: input left over")

def sc_sp.of(r: Wr.Dec<FSc.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      sc_sp.whole(q, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("screen: malformed request")

# the entry's answer to the input s
def sc_spec(s: String) -> String:
  sc_sp.of(sc_sp_req(s))

# LAW screen_ffi_exact (compiled core): on every input the interface's
# entry answers the spec: for a run the transcript after the frame's
# events (Open adds an active empty block with the next id; Grow lengthens
# each active block of its id, up to 2^32 - 1 characters; Fin makes
# each active block of its id final; Flush commits the final blocks from
# the start up to the first active one; Resize sets the width); for a pace
# the characters received and those a frame shows (the plain formula of
# pace_reveal_formula); for a stack each child's row and visible height;
# for a paint the first passing check's frame, Kept after three failed,
# else a request for the next check; and exactly "screen: more than three
# checks", "screen: input left over" or "screen: malformed request"
# otherwise
# EXCLUDES: a block changed by an event of another id, a committed block
#   changed, a flush past an active block, an Open with another id, a
#   pace or a stack by another rule, a paint before its check, a field
#   misread, a reply spelled otherwise, a default for malformed input,
#   input left over ignored, another error text
law screen_ffi_exact:
  for +s: String
  {FSc.ffi(s) == sc_spec(s) : String}
