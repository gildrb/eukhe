# eukhe: the laws of area infer_threshold

import Base
import ../bend/infer.bend as If
import ../bend/infer_threshold.bend as M
import ../bend/ffi_infer_threshold.bend as FT
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6.6) Early compaction, one request at a time
# ----------------------------------------------
# The model `first_at` in bend/infer.bend section
# 5; the harness asks the compiled core (bend/ffi_infer_threshold.bend)
# which threshold each request's context is over. Every input is free:
# compaction on or off, any token count, window, reserve and margin.

# The decision, independently, on whole numbers: with compaction on and
# a window w > 0, a context of t tokens is over the blocking threshold
# when t + reserve > w (the code compares strictly), else over the
# background threshold when the margin is positive and t + reserve +
# margin > w, else over none; with compaction off or the window unknown
# (0) over none. A reserve or margin Up{n} is n, Down{n} is -(1+n).

# t + r > w
def above(t: Nat, r: M.Z, w: Nat) -> Bool:
  match r:
    case M.Up{a}:
      Nat.is_lt(w, Nat.add(a, t))
    case M.Down{a}:
      Nat.is_lt(Nat.add(1n+a, w), t)

# t + r + c > w, for a margin c > 0
def above_by(t: Nat, r: M.Z, c: Nat, w: Nat) -> Bool:
  match r:
    case M.Up{a}:
      Nat.is_lt(w, Nat.add(a, Nat.add(c, t)))
    case M.Down{a}:
      Nat.is_lt(Nat.add(1n+a, w), Nat.add(c, t))

def over_spec.early(b: Bool) -> M.Over:
  match b:
    case True{}:
      M.Early{}
    case False{}:
      M.Under{}

def over_spec.margin(+t: Nat, +r: M.Z, m: M.Z, +w: Nat) -> M.Over:
  match m:
    case M.Up{c}:
      match c:
        case 0n:
          M.Under{}
        case 1n+b:
          over_spec.early(above_by(t, r, 1n+b, w))
    case M.Down{c}:
      M.Under{}

def over_spec.on(blocks: Bool, +t: Nat, +r: M.Z, m: M.Z, +w: Nat) -> M.Over:
  match blocks:
    case True{}:
      M.Blocks{}
    case False{}:
      over_spec.margin(t, r, m, w)

def over_spec(on: Bool, +t: Nat, w: Nat, +r: M.Z, m: M.Z) -> M.Over:
  match on:
    case False{}:
      M.Under{}
    case True{}:
      match w:
        case 0n:
          M.Under{}
        case 1n++v:
          over_spec.on(above(t, r, 1n+v), t, r, m, 1n+v)

# LAW infer_threshold_over_exact: the threshold a context is over is exactly: none with compaction off or the window unknown; blocking when tokens + reserve > window; else background when the margin is positive and tokens + reserve + margin > window; else none
law infer_threshold_over_exact:
  for on: Bool
  for +t: Nat
  for w: Nat
  for +r: M.Z
  for m: M.Z
  {M.over(on, t, w, r, m) == over_spec(on, t, w, r, m) : M.Over}

# the threshold `first_at` reads for the limit window - r: the least whole
# count over it, at least 0
def lim_spec(w: Nat, r: M.Z) -> Nat:
  match r:
    case M.Up{a}:
      Nat.sub(1n+w, a)
    case M.Down{a}:
      Nat.add(2n+a, w)

def is_blocks(o: M.Over) -> Bool:
  match o:
    case M.Blocks{}:
      True{}
    case M.Early{}:
      False{}
    case M.Under{}:
      False{}

def is_over(o: M.Over) -> Bool:
  match o:
    case M.Blocks{}:
      True{}
    case M.Early{}:
      True{}
    case M.Under{}:
      False{}

# the first context of xs is over the blocking threshold (b) or any
# threshold
def head.blocks(xs: List<&2, Nat>, +w: Nat, +r: M.Z, +m: M.Z) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      is_blocks(M.over(True{}, x, w, r, m))

def head.over(xs: List<&2, Nat>, +w: Nat, +r: M.Z, +m: M.Z) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      is_over(M.over(True{}, x, w, r, m))

# the requests of a run as the harness asks them, the first at index i:
# the index of the first over the blocking threshold (hit: the first of
# xs is), or over any threshold
def first_blocks(xs: List<&2, Nat>, +i: Nat, +w: Nat, +r: M.Z, +m: M.Z, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          first_blocks(rest, 1n+i, w, r, m, head.blocks(rest, w, r, m))

def first_over(xs: List<&2, Nat>, +i: Nat, +w: Nat, +r: M.Z, +m: M.Z, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          first_over(rest, 1n+i, w, r, m, head.over(rest, w, r, m))

# LAW infer_threshold_blocks_steps: over a run of requests (context sizes xs), with a known window, the first the entry finds over the blocking threshold is `first_at` at the limit window - reserve + 1, whatever the margin
law infer_threshold_blocks_steps:
  for +xs: List<&2, Nat>
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  {first_blocks(xs, 0n, 1n+v, r, m, head.blocks(xs, 1n+v, r, m)) == If.first_at(xs, lim_spec(1n+v, r), 0n) : Maybe<&2, Nat>}

# LAW infer_threshold_early_steps: with a positive margin c, the first request the entry finds over any threshold is `first_at` at the background threshold window - reserve - c + 1: so every law of `first_at` (compact_starts_early) holds for them
law infer_threshold_early_steps:
  for +xs: List<&2, Nat>
  for +v: Nat
  for +r: M.Z
  for +b: Nat
  {first_over(xs, 0n, 1n+v, r, M.Up{1n+b}, head.over(xs, 1n+v, r, M.Up{1n+b})) == If.first_at(xs, Nat.sub(lim_spec(1n+v, r), 1n+b), 0n) : Maybe<&2, Nat>}

# The entry (bend/ffi_infer_threshold.bend)
# -----------------------------------------
# The spellers write what Rust writes, with the wire primitives only.

def spell_z(z: M.Z, rest: String) -> String:
  match z:
    case M.Up{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case M.Down{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a request: on, tokens, window, reserve, margin
def spell_req(on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z) -> String:
  Wr.put_bool(on, Wr.put_nat(t, Wr.put_nat(w, spell_z(r, spell_z(m, "")))))

# what Rust reads: 0 none | 1 background | 2 blocking
def spell_over(o: M.Over) -> String:
  match o:
    case M.Under{}:
      Wr.put_nat(0n, "")
    case M.Early{}:
      Wr.put_nat(1n, "")
    case M.Blocks{}:
      Wr.put_nat(2n, "")

def z_fits(z: M.Z) -> Bool:
  match z:
    case M.Up{n}:
      LawsBase.wire_fits(n)
    case M.Down{n}:
      LawsBase.wire_fits(n)

# every number of a request fits the wire
def req_fits(t: Nat, w: Nat, r: M.Z, m: M.Z) -> Bool:
  Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(w), Bool.and(z_fits(r), z_fits(m))))

# Reader: the requests the entry accepts, read with the wire primitives
type Ask is Data:
  Ask{on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z}

def read_z.up(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{M.Up{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_z.down(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{M.Down{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_z.tag(t: Nat, s: String) -> Wr.Dec<M.Z>:
  match t:
    case 0n:
      read_z.up(Wr.get_nat(s))
    case 1n:
      read_z.down(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_z(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{t, s}:
      read_z.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.margin(on: Bool, t: Nat, w: Nat, r: M.Z, d: Wr.Dec<M.Z>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{m, s}:
      Wr.Got{Ask{on, t, w, r, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.reserve(on: Bool, t: Nat, w: Nat, d: Wr.Dec<M.Z>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{r, s}:
      read_ask.margin(on, t, w, r, read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.window(on: Bool, t: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{w, s}:
      read_ask.reserve(on, t, w, read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tokens(on: Bool, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{t, s}:
      read_ask.window(on, t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.go(d: Wr.Dec<Bool>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{on, s}:
      read_ask.tokens(on, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Ask) -> Maybe<&2, Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(d: Wr.Dec<Ask>) -> Maybe<&2, Ask>:
  match d:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Ask>:
  read_ask.whole(read_ask.go(Wr.get_bool(s)))

# LAW infer_threshold_ffi_answers: for every request whose numbers fit the wire, the entry answers the model's threshold
law infer_threshold_ffi_answers:
  for +on: Bool
  for +t: Nat
  for +w: Nat
  for +r: M.Z
  for +m: M.Z
  for fits: {req_fits(t, w, r, m) == True{} : Bool}
  {FT.ffi(spell_req(on, t, w, r, m)) == spell_over(M.over(on, t, w, r, m)) : String}

# LAW infer_threshold_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "infer_threshold: malformed request"
law infer_threshold_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Ask>}
  {FT.ffi(s) == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}

# LAW infer_threshold_ffi_example: anchor: the bytes Rust sends and reads, window 10 and reserve 2 (limit 8), margin 3: 5 tokens are under, 6 over the background threshold, 9 over the blocking one; no margin, 8 tokens are under; compaction off or the window unknown, none; a negative reserve -3 (limit 13) blocks at 14 only; a negative margin never runs early; a reserve past the window blocks every context; an unknown tag and input left over are refused
law infer_threshold_ffi_example:
  {FT.ffi("T5,10,0,2,0,3,") == "0," : String} &
  {FT.ffi("T6,10,0,2,0,3,") == "1," : String} &
  {FT.ffi("T9,10,0,2,0,3,") == "2," : String} &
  {FT.ffi("T8,10,0,2,0,0,") == "0," : String} &
  {FT.ffi("F99,10,0,2,0,3,") == "0," : String} &
  {FT.ffi("T99,0,0,2,0,3,") == "0," : String} &
  {FT.ffi("T13,10,1,2,0,0,") == "0," : String} &
  {FT.ffi("T14,10,1,2,0,0,") == "2," : String} &
  {FT.ffi("T8,10,0,2,1,0,") == "0," : String} &
  {FT.ffi("T0,10,0,11,0,0,") == "2," : String} &
  {FT.ffi("T5,10,0,2,2,3,") == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String} &
  {FT.ffi("T5,10,0,2,0,3,x") == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}
