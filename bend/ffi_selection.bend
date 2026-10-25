# ffi_selection: the stepper of the compiled Bend core for the fullscreen
# chat's text selection (crates/eukhe-tui/src/selection.rs): its state is
# the selection of bend/selection.bend, kept in the Bend heap; each step
# is one input (`M.step`), and the reply is what Rust shows, copies and
# scrolls. The codec is the wire format of bend/wire.bend:
#
#   open     (nothing)                      reply: Out (nothing selected)
#   step     Ev                             reply: Out
#   Ev       0, Cell, time, Gs (press) | 1, Cell, lo, hi (drag)
#            | 2, count, Row... (release) | 3 (key) | 4 (Esc) | 5 (wheel)
#            | 6 (content changed)
#   Cell     row, col
#   Row      Wrap, Gs
#   Wrap     0 single | 1 head | 2 continuation
#   Gs       count, glyph...                (0 a blank, w >= 1 w cells wide)
#   Out      Sel, Copy, Pan, eat: Bool
#   Sel      0 (none) | 1, Cell, Cell       (start, end; both in)
#   Copy     0 (none) | 1, count, Piece...
#   Piece    row, from, to, nl: Bool        (glyphs from..to-1 of release row
#                                            `row`, after a newline when nl)
#   Pan      0 none | 1 up | 2 down
#
# A malformed input, or one with input left over, answers the wire's
# error form and keeps the state; an open with input opens the refused
# state, which answers every step with the error form.

import Base
import ./wire.bend as W
import ./selection.bend as M

# Decoders
# --------

def get_cell.col(row: Nat, r: W.Dec<Nat>) -> W.Dec<M.Cell>:
  match r:
    case W.Got{col, s}:
      W.Got{M.Cell{row, col}, s}
    case W.Bad{}:
      W.Bad{}

def get_cell.row(r: W.Dec<Nat>) -> W.Dec<M.Cell>:
  match r:
    case W.Got{row, s}:
      get_cell.col(row, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cell(s: String) -> W.Dec<M.Cell>:
  get_cell.row(W.get_nat(s))

def get_gs(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_wrap.tag(n: Nat, s: String) -> W.Dec<M.Wrap>:
  match n:
    case 0n:
      W.Got{M.Single{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Head{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{M.Cont{}, s}
            case 1n+c:
              W.Bad{}

def get_wrap.go(r: W.Dec<Nat>) -> W.Dec<M.Wrap>:
  match r:
    case W.Got{n, s}:
      get_wrap.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_wrap(s: String) -> W.Dec<M.Wrap>:
  get_wrap.go(W.get_nat(s))

def get_row.gs(w: M.Wrap, r: W.Dec<List<&2, Nat>>) -> W.Dec<M.Row>:
  match r:
    case W.Got{gs, s}:
      W.Got{M.Row{w, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_row.wrap(r: W.Dec<M.Wrap>) -> W.Dec<M.Row>:
  match r:
    case W.Got{w, s}:
      get_row.gs(w, get_gs(s))
    case W.Bad{}:
      W.Bad{}

def get_row(s: String) -> W.Dec<M.Row>:
  get_row.wrap(get_wrap(s))

def get_ev.gs(at: M.Cell, t: Nat, r: W.Dec<List<&2, Nat>>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{gs, s}:
      W.Got{M.EvPress{at, t, gs}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.time(at: M.Cell, r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.gs(at, t, get_gs(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.press(r: W.Dec<M.Cell>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{at, s}:
      get_ev.time(at, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.hi(at: M.Cell, lo: Nat, r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{hi, s}:
      W.Got{M.EvDrag{at, lo, hi}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.lo(at: M.Cell, r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{lo, s}:
      get_ev.hi(at, lo, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.drag(r: W.Dec<M.Cell>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{at, s}:
      get_ev.lo(at, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.rows(r: W.Dec<List<&2, M.Row>>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{rows, s}:
      W.Got{M.EvRelease{rows}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<M.Ev>:
  match n:
    case 0n:
      get_ev.press(get_cell(s))
    case 1n+a:
      match a:
        case 0n:
          get_ev.drag(get_cell(s))
        case 1n+b:
          match b:
            case 0n:
              get_ev.rows(W.get_list(~M.Row, ~get_row, s))
            case 1n+c:
              match c:
                case 0n:
                  W.Got{M.EvKey{}, s}
                case 1n+d:
                  match d:
                    case 0n:
                      W.Got{M.EvEsc{}, s}
                    case 1n+e:
                      match e:
                        case 0n:
                          W.Got{M.EvWheel{}, s}
                        case 1n+f:
                          match f:
                            case 0n:
                              W.Got{M.EvChanged{}, s}
                            case 1n+g:
                              W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<M.Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<M.Ev>:
  get_ev.go(W.get_nat(s))

# Encoders
# --------

def put_cell(c: M.Cell, rest: String) -> String:
  match c:
    case M.Cell{row, col}:
      W.put_nat(row, W.put_nat(col, rest))

def put_sel(m: Maybe<&2, M.Rng>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{r}:
      match r:
        case M.Rng{a, b}:
          W.put_nat(1n, put_cell(a, put_cell(b, rest)))

def put_piece(p: M.Piece, rest: String) -> String:
  match p:
    case M.Piece{row, from, to, nl}:
      W.put_nat(row, W.put_nat(from, W.put_nat(to, W.put_bool(nl, rest))))

def put_copy(m: Maybe<&2, List<&2, M.Piece>>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{ps}:
      W.put_nat(1n, W.put_list(~M.Piece, ~put_piece, ps, rest))

def put_pan(p: M.Pan, rest: String) -> String:
  match p:
    case M.PanNone{}:
      W.put_nat(0n, rest)
    case M.PanUp{}:
      W.put_nat(1n, rest)
    case M.PanDown{}:
      W.put_nat(2n, rest)

def put_out(o: M.Out, rest: String) -> String:
  match o:
    case M.Out{s, c, p, e}:
      put_sel(s, put_copy(c, put_pan(p, W.put_bool(e, rest))))

# The stepper
# -----------

# the selection of the chat surface, or a refused open
type St is Data:
  Live{s: M.St}
  Refused{}

def open.go(done: Bool) -> St & String:
  match done:
    case True{}:
      (Live{M.start()}, put_out(M.Out{None{}, None{}, M.PanNone{}, False{}}, ""))
    case False{}:
      (Refused{}, W.err("selection: open takes no input"))

# open: nothing selected
def open(input: String) -> St & String:
  open.go(W.end(input))

def step.res(r: M.Res) -> St & String:
  match r:
    case M.Res{s, o}:
      (Live{s}, put_out(o, ""))

def step.end(done: Bool, s: M.St, e: M.Ev) -> St & String:
  match done:
    case True{}:
      step.res(M.step(s, e))
    case False{}:
      (Live{s}, W.err("selection: input left over"))

def step.ev(s: M.St, r: W.Dec<M.Ev>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), s, e)
    case W.Bad{}:
      (Live{s}, W.err("selection: malformed event"))

# step: one input of the selection; the reply is what to show, copy and
# scroll
def step(st: St, input: String) -> St & String:
  match st:
    case Live{s}:
      step.ev(s, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("selection: the open was refused"))
