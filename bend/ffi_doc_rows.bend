# ffi_doc_rows: the entry of the compiled Bend core for what a read of a
# file shows (bend/doc_rows.bend `gate`, `view`; Rust:
# crates/eukhe-docs/src/read/mod.rs). Pure: no IO, no @unsafe, no foreign
# effect.
#
# Requests (a tag, then the fields):
#   0 gate   raw, utf8, utf16, nul: Bool
#            reply: Gate (tag 0 Go | 1 NotUtf8 | 2 Binary)
#   1 view   sel: Sel, utf8: Bool, over: Bool, the projection
#            (bend/ffi_doc_lines.bend: bom: Bool, List<Line>)
#            reply: total: Nat, raw: Bool, List<Span>, List<Note>, tag: Bool
# Sel = 0 Whole | 1 Raw | 2 Lines (List<Range>, raw: Bool);
# Range = start: Nat, end: Maybe<Nat> (0 | 1 then the Nat);
# Span = start: Nat, end: Nat, gap: Bool;
# Note = 0 Beyond (line) | 1 Remain (count, next) | 2 RangeBeyond (start,
# Maybe<Nat> end) | 3 TooBig.
# A malformed request, or one with input left over, answers the wire
# error form.

import Base
import ./wire.bend as W
import ./doc_lines.bend as Dl
import ./ffi_doc_lines.bend as Fl
import ./doc_rows.bend as M

# Maybe<Nat>
# ----------

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mnat.some(W.get_nat(s))
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.tag(W.get_nat(s))

# Sel
# ---

def get_range.end(st: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.Range>:
  match r:
    case W.Got{m, s}:
      W.Got{M.Range{st, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_range.start(r: W.Dec<Nat>) -> W.Dec<M.Range>:
  match r:
    case W.Got{st, s}:
      get_range.end(st, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_range(s: String) -> W.Dec<M.Range>:
  get_range.start(W.get_nat(s))

def get_sel.raw(xs: List<&2, M.Range>, r: W.Dec<Bool>) -> W.Dec<M.Sel>:
  match r:
    case W.Got{raw, s}:
      W.Got{M.Lines{xs, raw}, s}
    case W.Bad{}:
      W.Bad{}

def get_sel.ranges(r: W.Dec<List<&2, M.Range>>) -> W.Dec<M.Sel>:
  match r:
    case W.Got{xs, s}:
      get_sel.raw(xs, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_sel.tag(r: W.Dec<Nat>) -> W.Dec<M.Sel>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{M.Whole{}, s}
        case 1n:
          W.Got{M.Raw{}, s}
        case 2n:
          get_sel.ranges(W.get_list(~M.Range, ~get_range, s))
        case 3n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_sel(s: String) -> W.Dec<M.Sel>:
  get_sel.tag(W.get_nat(s))

# Replies
# -------

def put_gate(g: M.Gate) -> String:
  match g:
    case M.Go{}:
      W.put_nat(0n, "")
    case M.NotUtf8{}:
      W.put_nat(1n, "")
    case M.Binary{}:
      W.put_nat(2n, "")

def put_span(x: M.Span, rest: String) -> String:
  match x:
    case M.Span{s, e, g}:
      W.put_nat(s, W.put_nat(e, W.put_bool(g, rest)))

def put_note(n: M.Note, rest: String) -> String:
  match n:
    case M.Beyond{l}:
      W.put_nat(0n, W.put_nat(l, rest))
    case M.Remain{c, x}:
      W.put_nat(1n, W.put_nat(c, W.put_nat(x, rest)))
    case M.RangeBeyond{s, m}:
      W.put_nat(2n, W.put_nat(s, put_mnat(m, rest)))
    case M.TooBig{}:
      W.put_nat(3n, rest)

def put_view(v: M.View) -> String:
  match v:
    case M.View{t, raw, sp, ns, tag}:
      W.put_nat(t, W.put_bool(raw, W.put_list(~M.Span, ~put_span, sp, W.put_list(~M.Note, ~put_note, ns, W.put_bool(tag, "")))))

# The requests
# ------------

def gate.done(raw: Bool, u8: Bool, u16: Bool, nul: Bool, done: Bool) -> String:
  match done:
    case True{}:
      put_gate(M.gate(raw, u8, u16, nul))
    case False{}:
      W.err("doc_rows: input left over")

def gate.nul(raw: Bool, u8: Bool, u16: Bool, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{nul, s}:
      gate.done(raw, u8, u16, nul, W.end(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def gate.u16(raw: Bool, u8: Bool, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{u16, s}:
      gate.nul(raw, u8, u16, W.get_bool(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def gate.u8(raw: Bool, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{u8, s}:
      gate.u16(raw, u8, W.get_bool(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def gate.raw(r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{raw, s}:
      gate.u8(raw, W.get_bool(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def view.done(sel: M.Sel, u8: Bool, over: Bool, p: Dl.Proj, done: Bool) -> String:
  match done:
    case True{}:
      put_view(M.view(sel, u8, over, p))
    case False{}:
      W.err("doc_rows: input left over")

def view.proj(sel: M.Sel, u8: Bool, over: Bool, r: W.Dec<Dl.Proj>) -> String:
  match r:
    case W.Got{p, s}:
      view.done(sel, u8, over, p, W.end(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def view.over(sel: M.Sel, u8: Bool, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{over, s}:
      view.proj(sel, u8, over, Fl.get_proj(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def view.u8(sel: M.Sel, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{u8, s}:
      view.over(sel, u8, W.get_bool(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def view.sel(r: W.Dec<M.Sel>) -> String:
  match r:
    case W.Got{sel, s}:
      view.u8(sel, W.get_bool(s))
    case W.Bad{}:
      W.err("doc_rows: malformed request")

def run(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          gate.raw(W.get_bool(s))
        case 1n:
          view.sel(get_sel(s))
        case 2n+p:
          W.err("doc_rows: malformed request")
    case W.Bad{}:
      W.err("doc_rows: malformed request")

# the entry: a read's gate, or what it shows
def ffi(input: String) -> String:
  run(W.get_nat(input))
