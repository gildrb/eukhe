# screen: the model of the interface.
#
# 1. The transcript. A block of the transcript is active (it still
#    grows), final (its text is fixed), or committed (it is in the
#    terminal's native scrollback). A flush commits final blocks in order,
#    up to the first active block. Committed text is never written again:
#    a resize keeps the scrollback as it is (policy "preserve") and draws
#    only the live region again. Committed blocks are inert (law
#    tx_committed_inert), so the compiled core runs the events of a frame
#    on the blocks after the committed prefix alone.
# 2. Pacing. Streamed text arrives in chunks of any size. Each frame
#    shows more of it: at least `min` characters (when there is backlog)
#    and a share 1/(1+k) of the backlog when that is more. The screen
#    never shows text that did not arrive, and it never shows less than
#    before. The share forms 1 + k only when k is below the backlog, so a
#    lag saturated at the core's cap (2^48 - 1) never overflows.
# 3. Off-screen verification. A frame is drawn off screen first and
#    checked. A frame that fails the check is drawn again in full and
#    checked again. Only a checked frame reaches the terminal; a frame
#    that fails both checks is reported, not shown.
# 4. Layout. A vertical stack places its children one under the other,
#    from the top of the viewport, clipped to its height.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters).

import Base

# 1. The transcript
# -----------------

type St is Data:
  Active{}
  Final{}
  Comm{}

type Blk is Data:
  Blk{id: Nat, st: St, len: Nat}

type Ev is Data:
  Open{}                # a new block starts, active
  Grow{id: Nat, n: Nat} # block id gets n more characters
  Fin{id: Nat}          # block id is final
  Flush{}               # commit the final blocks, in order
  Resize{w: Nat}        # the terminal has a new width

# The transcript: the blocks in the order they opened, the next id, the
# width
type Tx is Data:
  Tx{blocks: List<&2, Blk>, next: Nat, width: Nat}

def Tx.blocks(t: Tx) -> List<&2, Blk>:
  match t:
    case Tx{b, n, w}:
      b

def Blk.id(b: Blk) -> Nat:
  match b:
    case Blk{i, s, l}:
      i

# the first block of bs has id x
def bid.at(+bs: List<&2, Blk>, +x: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> rest:
      Nat.is_eq(Blk.id(b), x)

# block b grows by n when it is active
def grow1(b: Blk, +n: Nat) -> Blk:
  match b:
    case Blk{i, s, l}:
      match s:
        case Active{}:
          Blk{i, Active{}, Nat.add(l, n)}
        case Final{}:
          Blk{i, Final{}, l}
        case Comm{}:
          Blk{i, Comm{}, l}

# block b is final when it was active
def fin1(b: Blk) -> Blk:
  match b:
    case Blk{i, s, l}:
      match s:
        case Active{}:
          Blk{i, Final{}, l}
        case Final{}:
          Blk{i, Final{}, l}
        case Comm{}:
          Blk{i, Comm{}, l}

def edit.one(b: Blk, g: Maybe<&2, Nat>) -> Blk:
  match g:
    case None{}:
      fin1(b)
    case Some{n}:
      grow1(b, n)

# change block x of bs with grow (Some{n}) or fin (None); hit is
# bid.at(bs, x)
def edit.go(bs: List<&2, Blk>, +x: Nat, +g: Maybe<&2, Nat>, hit: Bool) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> +rest:
      match hit:
        case True{}:
          edit.one(b, g) <> edit.go(rest, x, g, bid.at(rest, x))
        case False{}:
          b <> edit.go(rest, x, g, bid.at(rest, x))

def edit(+bs: List<&2, Blk>, +x: Nat, +g: Maybe<&2, Nat>) -> List<&2, Blk>:
  edit.go(bs, x, g, bid.at(bs, x))

# commit final blocks from the start, up to the first active block
def flush(bs: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Blk{i, s, l}:
          match s:
            case Comm{}:
              Blk{i, Comm{}, l} <> flush(rest)
            case Final{}:
              Blk{i, Comm{}, l} <> flush(rest)
            case Active{}:
              Blk{i, Active{}, l} <> rest

def step(t: Tx, e: Ev) -> Tx:
  match t:
    case Tx{bs, +n, w}:
      match e:
        case Open{}:
          Tx{List.append(&2, Blk, bs, [Blk{n, Active{}, 0n}]), 1n+n, w}
        case Grow{x, k}:
          Tx{edit(bs, x, Some{k}), n, w}
        case Fin{x}:
          Tx{edit(bs, x, None{}), n, w}
        case Flush{}:
          Tx{flush(bs), n, w}
        case Resize{v}:
          Tx{bs, n, v}

def run(es: List<&2, Ev>, t: Tx) -> Tx:
  match es:
    case Nil{}:
      t
    case e <> rest:
      run(rest, step(t, e))

# a line of the scrollback: a committed block's id and length
type Line is Data:
  Line{id: Nat, len: Nat}

# the scrollback: the committed blocks (id and length), in order, up to
# the first block that is not committed
def scroll(bs: List<&2, Blk>) -> List<&2, Line>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Blk{i, s, l}:
          match s:
            case Comm{}:
              Line{i, l} <> scroll(rest)
            case Final{}:
              Nil{}
            case Active{}:
              Nil{}

# the committed blocks of bs come first: no committed block after one
# that is not committed
def gapless.go(bs: List<&2, Blk>, +seen: Bool) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      match b:
        case Blk{i, s, l}:
          match s:
            case Comm{}:
              Bool.and(Bool.not(seen), gapless.go(rest, seen))
            case Final{}:
              gapless.go(rest, True{})
            case Active{}:
              gapless.go(rest, True{})

def gapless(bs: List<&2, Blk>) -> Bool:
  gapless.go(bs, False{})

# the first block of bs that is not committed is active (or there is
# none): nothing final waits behind a flush
def flushed(bs: List<&2, Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      match b:
        case Blk{i, s, l}:
          match s:
            case Comm{}:
              flushed(rest)
            case Final{}:
              False{}
            case Active{}:
              True{}

# xs is a prefix of ys
def pre(xs: List<&2, Line>, ys: List<&2, Line>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Line{a, b} <> xr:
      match ys:
        case Nil{}:
          False{}
        case Line{c, d} <> yr:
          Bool.and(Bool.and(Nat.is_eq(a, c), Nat.is_eq(b, d)), pre(xr, yr))

# 2. Pacing
# ---------

type PEv is Data:
  Chunk{n: Nat}  # n characters arrive
  Frame{}        # the renderer draws a frame

# what arrived and what the screen shows
type Pace is Data:
  Pace{recv: Nat, shown: Nat}

def Pace.recv(p: Pace) -> Nat:
  match p:
    case Pace{r, s}:
      r

def Pace.shown(p: Pace) -> Nat:
  match p:
    case Pace{r, s}:
      s

# the share 1/(1+k) of a backlog b. When k >= b the share is 0 (b/(1+k)
# is 0) and 1 + k is not formed, so a lag at the cap of the compiled
# core's numbers (2^48 - 1) never overflows
def share.at(below: Bool, +k: Nat, +b: Nat) -> Nat:
  match below:
    case True{}:
      Nat.div(b, 1n+k)
    case False{}:
      0n

def share(+k: Nat, +b: Nat) -> Nat:
  share.at(Nat.is_lt(k, b), k, b)

# the characters one frame adds, with backlog b
def reveal(+min: Nat, +k: Nat, +b: Nat) -> Nat:
  Nat.min(b, Nat.max(min, share(k, b)))

def pace.step(+min: Nat, +k: Nat, p: Pace, e: PEv) -> Pace:
  match p:
    case Pace{+r, +s}:
      match e:
        case Chunk{n}:
          Pace{Nat.add(r, n), s}
        case Frame{}:
          Pace{r, Nat.add(s, reveal(min, k, Nat.sub(r, s)))}

def pace.run(es: List<&2, PEv>, +min: Nat, +k: Nat, p: Pace) -> Pace:
  match es:
    case Nil{}:
      p
    case e <> rest:
      pace.run(rest, min, k, pace.step(min, k, p, e))

def frames(n: Nat) -> List<&2, PEv>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Frame{} <> frames(m)

# 3. Off-screen verification
# --------------------------

type Shown is Data:
  Drawn{frame: Nat, full: Bool}  # the terminal got frame (full: redrawn in full)
  Error{frame: Nat}              # both checks failed; nothing was drawn

# a frame f (its full redraw g) with the two checks' results
def present(f: Nat, g: Nat, ok1: Bool, ok2: Bool) -> Shown:
  match ok1:
    case True{}:
      Drawn{f, False{}}
    case False{}:
      match ok2:
        case True{}:
          Drawn{g, True{}}
        case False{}:
          Error{f}

# a frame reached the terminal only after a check passed
def checked(s: Shown, ok1: Bool, ok2: Bool) -> Bool:
  match s:
    case Drawn{f, full}:
      match full:
        case False{}:
          ok1
        case True{}:
          ok2
    case Error{f}:
      Bool.not(Bool.or(ok1, ok2))

# what reaches the terminal after present
type Paint is Data:
  Put{frame: Nat, full: Bool}  # present drew frame (full: redrawn in full)
  Fresh{frame: Nat}            # both checks failed; frame, the fresh redraw on
                               # a blank screen, passed the third check
  Kept{frame: Nat}             # all three failed: nothing drawn; the surface
                               # goes on

# present's decision s, then the fresh redraw h with the third check's
# result ok3
def resync(s: Shown, h: Nat, ok3: Bool) -> Paint:
  match s:
    case Drawn{f, full}:
      Put{f, full}
    case Error{f}:
      match ok3:
        case True{}:
          Fresh{h}
        case False{}:
          Kept{f}

# 4. Layout
# ---------

# A placed child: its top row and its visible height
type Rect is Data:
  Rect{y: Nat, h: Nat}

# place children of heights hs from row y in a viewport of `rows` rows
def vstack(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> List<&2, Rect>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Rect{y, Nat.min(h, Nat.sub(rows, y))} <> vstack(rest, Nat.add(y, h), rows)

# every rect ends inside the viewport
def inside(rs: List<&2, Rect>, +rows: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      match r:
        case Rect{y, +h}:
          Bool.and(Bool.or(Nat.is_eq(h, 0n), Nat.is_le(Nat.add(y, h), rows)), inside(rest, rows))

# each rect starts at or below the end of the one before it (from y)
def apart(rs: List<&2, Rect>, +y: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      match r:
        case Rect{+ry, rh}:
          Bool.and(Nat.is_le(y, ry), apart(rest, Nat.add(ry, rh)))

# the visible heights of rs
def heights(rs: List<&2, Rect>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Rect{y, h}:
          h <> heights(rest)

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, sum(rest))
