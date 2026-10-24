import Base
import ./wire.bend as W
import ./infer_guard.bend as M

# ffi_infer_guard: the stepper of the compiled Bend core for the
# repetition guard of one stream (bend/infer_guard.bend `feed`;
# bend/infer.bend section 4). Its state, the guard, stays in the Bend heap:
# Rust (crates/eukhe-ai utils/stream_repeat.rs) cuts the stream into lines
# and sends one id per line (equal lines, equal ids), the model decides.
#
#   open   k: Nat (the window)            reply: empty
#   step   x: Nat (the next chunk's id)   reply: 0 (kept) | 1, at: Nat, period: Nat (cut)
#
# A cut stream stays cut: every later step answers the same cut. A
# malformed chunk, or one with input left over, answers the wire's error
# form and keeps the guard; an open with a malformed window opens the
# refused state, which answers every step with the error form.

# Encoding
# --------

# a cut after `at` chunks with period p
def put_cut(at: Nat, p: Nat) -> String:
  W.put_nat(1n, W.put_nat(at, W.put_nat(p, "")))

# The stepper
# -----------

# the guard, a cut stream, or a refused open
type St is Data:
  Live{g: M.St}
  Ended{at: Nat, period: Nat}
  Shut{}

def open.end(whole: Bool, k: Nat) -> St & String:
  match whole:
    case True{}:
      (Live{M.start(k)}, "")
    case False{}:
      (Shut{}, W.err("infer_guard: malformed window"))

def open.go(d: W.Dec<Nat>) -> St & String:
  match d:
    case W.Got{k, s}:
      open.end(W.end(s), k)
    case W.Bad{}:
      (Shut{}, W.err("infer_guard: malformed window"))

# open: a guard with the window of the input that read nothing yet
def open(input: String) -> St & String:
  open.go(W.get_nat(input))

def step.of(n: M.Next) -> St & String:
  match n:
    case M.Goes{g}:
      (Live{g}, W.put_nat(0n, ""))
    case M.Cuts{+at, +p}:
      (Ended{at, p}, put_cut(at, p))

def step.end(whole: Bool, g: M.St, x: Nat) -> St & String:
  match whole:
    case True{}:
      step.of(M.feed(g, x))
    case False{}:
      (Live{g}, W.err("infer_guard: malformed chunk"))

def step.chunk(g: M.St, d: W.Dec<Nat>) -> St & String:
  match d:
    case W.Got{x, s}:
      step.end(W.end(s), g, x)
    case W.Bad{}:
      (Live{g}, W.err("infer_guard: malformed chunk"))

# step: one chunk of the stream; the reply is whether it cut the stream
def step(st: St, input: String) -> St & String:
  match st:
    case Live{g}:
      step.chunk(g, W.get_nat(input))
    case Ended{+at, +p}:
      (Ended{at, p}, put_cut(at, p))
    case Shut{}:
      (Shut{}, W.err("infer_guard: the open was refused"))
