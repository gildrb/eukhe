# ffi_tui_color: the terminal colors (bend/tui_color.bend: the effort ramp
# `ramp`, the usage band `band`, the color roles `roles`) as an entry of
# the compiled Bend core (crates/eukhe-bend/WIRE.md is the grammar).
# Request: a tag, then
#   0  a ramp: the low end's red, green and blue, the high end's, and the
#      rungs n                                   -> the n rungs (List of R, G, B)
#   1  a band: the tokens in use t, the window w -> the band (a Nat, 0 to 3)
#   2  the roles                                 -> the token index of every
#                                                   color slot (List<Nat>)
# A ramp with a channel above 255 or more than 255 rungs answers the error
# form "tui_color: a channel above 255 or more than 255 rungs" (no color
# has a wider channel; no ramp of more rungs has distinct colors); any
# other input that is not exactly one request answers the error form
# "tui_color: malformed request". laws/tui_color.bend (section entry)
# states this file's laws; PROOF.bend proves them. Pure: no IO, no @unsafe.
#
# The band runs without a product past the window: the model's test
# w * num <= t * den needs t * den, which passes the runtime's 2^48 - 1 for
# the largest t the wire carries; `need` asks instead whether t reaches
# ceil(w * num / den) = num * q + ceil(num * r / den), w = q * den + r.

import Base
import ./wire.bend as W
import ./tui_color.bend as TC

# A request of the entry
type Req is Data:
  QRamp{lo: TC.Px, hi: TC.Px, n: Nat}
  QBand{t: Nat, w: Nat}
  QRoles{}

# Decoding
# --------

def get_px.b(r: Nat, g: Nat, d: W.Dec<Nat>) -> W.Dec<TC.Px>:
  match d:
    case W.Got{b, s}:
      W.Got{TC.Px{r, g, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_px.g(r: Nat, d: W.Dec<Nat>) -> W.Dec<TC.Px>:
  match d:
    case W.Got{g, s}:
      get_px.b(r, g, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_px(d: W.Dec<Nat>) -> W.Dec<TC.Px>:
  match d:
    case W.Got{r, s}:
      get_px.g(r, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ramp.n(lo: TC.Px, hi: TC.Px, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{n, s}:
      W.Got{QRamp{lo, hi, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ramp.hi(lo: TC.Px, d: W.Dec<TC.Px>) -> W.Dec<Req>:
  match d:
    case W.Got{hi, s}:
      get_ramp.n(lo, hi, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ramp(d: W.Dec<TC.Px>) -> W.Dec<Req>:
  match d:
    case W.Got{lo, s}:
      get_ramp.hi(lo, get_px(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_band.w(t: Nat, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{w, s}:
      W.Got{QBand{t, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_band(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_band.w(t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_ramp(get_px(W.get_nat(s)))
    case 1n:
      get_band(W.get_nat(s))
    case 2n:
      W.Got{QRoles{}, s}
    case 3n+p:
      W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# The ramp's range
# ----------------

# the widest channel and the most rungs a ramp takes
def top() -> Nat:
  255n

def px.ok(p: TC.Px) -> Bool:
  match p:
    case TC.Px{r, g, b}:
      Bool.and(Nat.is_le(r, top()), Bool.and(Nat.is_le(g, top()), Nat.is_le(b, top())))

# every channel of lo and hi is at most 255, and n is at most 255
def ramp.ok(lo: TC.Px, hi: TC.Px, n: Nat) -> Bool:
  Bool.and(px.ok(lo), Bool.and(px.ok(hi), Nat.is_le(n, top())))

# The band
# --------

# the least tokens that reach num / (1 + dp) of a w-token window,
# ceil(w * num / (1 + dp)), as num * q + ceil(num * r / (1 + dp)) with
# w = q * (1 + dp) + r: with num at most 1 + dp no term passes w + num * dp
def need(+num: Nat, +dp: Nat, +w: Nat) -> Nat:
  Nat.add(Nat.mul(num, Nat.div(w, 1n+dp)), Nat.div(Nat.add(Nat.mul(num, Nat.mod(w, 1n+dp)), dp), 1n+dp))

# t of w tokens reach the fraction num / den of the window (TC.reached;
# a band of den 0, which the model has none of, is the model's test)
def reach.den(+num: Nat, den: Nat, +t: Nat, +w: Nat) -> Bool:
  match den:
    case 0n:
      TC.reached(TC.Frac{num, 0n}, t, w)
    case 1n+dp:
      Bool.and(Nat.is_lt(0n, w), Nat.is_le(need(num, dp, w), t))

def reach(f: TC.Frac, +t: Nat, +w: Nat) -> Bool:
  match f:
    case TC.Frac{num, den}:
      reach.den(num, den, t, w)

def band.go(fs: List<&2, TC.Frac>, +t: Nat, +w: Nat) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{f, rest}:
      Nat.add(TC.one(reach(f, t, w)), band.go(rest, t, w))

# the usage band of t of w tokens (TC.band), with no product past the
# window
def band(+t: Nat, +w: Nat) -> Nat:
  band.go(TC.bands(), t, w)

# Encoding
# --------

def put_px(p: TC.Px, rest: String) -> String:
  match p:
    case TC.Px{r, g, b}:
      W.put_nat(r, W.put_nat(g, W.put_nat(b, rest)))

def answer.ramp(ok: Bool, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> String:
  match ok:
    case True{}:
      W.put_list(~TC.Px, ~put_px, TC.ramp(lo, hi, n), "")
    case False{}:
      W.err("tui_color: a channel above 255 or more than 255 rungs")

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QRamp{+lo, +hi, +n}:
      answer.ramp(ramp.ok(lo, hi, n), lo, hi, n)
    case QBand{t, w}:
      W.put_nat(band(t, w), "")
    case QRoles{}:
      W.put_list(~Nat, ~W.put_nat, TC.roles(), "")

# The entry
# ---------

def fail() -> String:
  W.err("tui_color: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      fail()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_req(input))
