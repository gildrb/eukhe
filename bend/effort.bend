# effort: the model of the reasoning depth (thinking level) of a session
# (docs/inference.md, S10).
#
# 1. The ladder. The levels in order: off, minimal, low, medium, high,
#    xhigh, max. A model offers a sublist of the ladder. A model without
#    reasoning offers off only. A reasoning model keeps each level of the
#    ladder, in order, by its entry in the model's thinking-level map: a
#    null entry drops the level, a wire string keeps it, and a missing
#    entry keeps it unless the level is xhigh or max. A model with no map
#    is a map with every entry missing.
# 2. The clamp. A level that the model offers stays. Another level goes
#    to the first offered level up the ladder from it, else down the
#    ladder from it. With no offered level the clamp is off.
# 3. The cycle. With fewer than two offered levels a cycle step changes
#    nothing (None). Else it starts at the clamp of the current level and
#    takes the next offered level (forward) or the one before (backward),
#    and wraps at the ends.
# 4. The session. Open settles the stored level: the stored level (else
#    the default) fitted to the model; fitted is clamped when the model is
#    in the catalog, unchanged without a catalog model. A model switch
#    clamps the current level to the new model; a set fits the requested
#    level; a cycle step sets the level it gives. The runtime sends the
#    stored level (else off), fitted to the model. The display shows the
#    stored level fitted to the model, and `default` when no level is
#    stored.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

# 1. The ladder
# -------------

type Lv is Data:
  Off{}
  Minimal{}
  Low{}
  Medium{}
  High{}
  Xhigh{}
  Max{}

def Lv.idx(l: Lv) -> Nat:
  match l:
    case Off{}:
      0n
    case Minimal{}:
      1n
    case Low{}:
      2n
    case Medium{}:
      3n
    case High{}:
      4n
    case Xhigh{}:
      5n
    case Max{}:
      6n

def Lv.eq(a: Lv, b: Lv) -> Bool:
  Nat.is_eq(Lv.idx(a), Lv.idx(b))

def ladder() -> List<&2, Lv>:
  [Off{}, Minimal{}, Low{}, Medium{}, High{}, Xhigh{}, Max{}]

# xhigh and max: offered only with an explicit entry
def ext(l: Lv) -> Bool:
  match l:
    case Off{}:
      False{}
    case Minimal{}:
      False{}
    case Low{}:
      False{}
    case Medium{}:
      False{}
    case High{}:
      False{}
    case Xhigh{}:
      True{}
    case Max{}:
      True{}

# An entry of the thinking-level map
type Ent is Data:
  Missing{}  # the map has no entry for the level
  Null{}     # the entry is null: the model does not take the level
  Wire{}     # the entry is a wire string

type LvMap is Data:
  LvMap{off: Ent, minimal: Ent, low: Ent, medium: Ent, high: Ent, xhigh: Ent, max: Ent}

# the map with no entries (a model with no map)
def LvMap.none() -> LvMap:
  LvMap{Missing{}, Missing{}, Missing{}, Missing{}, Missing{}, Missing{}, Missing{}}

def entry(l: Lv, map: LvMap) -> Ent:
  match l:
    case Off{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          o
    case Minimal{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          mi
    case Low{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          lo
    case Medium{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          me
    case High{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          hi
    case Xhigh{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          xh
    case Max{}:
      match map:
        case LvMap{o, mi, lo, me, hi, xh, mx}:
          mx

# A model: reasoning or not, and its thinking-level map
type Mdl is Data:
  Mdl{reasoning: Bool, map: LvMap}

# whether a reasoning model keeps level l with entry e
def keep.e(l: Lv, e: Ent) -> Bool:
  match e:
    case Missing{}:
      Bool.not(ext(l))
    case Null{}:
      False{}
    case Wire{}:
      True{}

def keep(+map: LvMap, +l: Lv) -> Bool:
  keep.e(l, entry(l, map))

def cons_if(b: Bool, x: Lv, xs: List<&2, Lv>) -> List<&2, Lv>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

# the levels of xs that a reasoning model with map keeps, in order
def offer(+map: LvMap, xs: List<&2, Lv>) -> List<&2, Lv>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      cons_if(keep(map, x), x, offer(map, rest))

# the levels the model offers
def offered(m: Mdl) -> List<&2, Lv>:
  match m:
    case Mdl{reasoning, map}:
      match reasoning:
        case True{}:
          offer(map, ladder())
        case False{}:
          [Off{}]

def has(xs: List<&2, Lv>, +l: Lv) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Lv.eq(x, l), has(rest, l))

def empty(xs: List<&2, Lv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      False{}

# every level of xs is above index k
def above(+k: Nat, xs: List<&2, Lv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Nat.is_lt(k, Lv.idx(x)), above(k, rest))

# xs is strictly ascending in ladder order (so it has no duplicates)
def asc(xs: List<&2, Lv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(above(Lv.idx(x), rest), asc(rest))

# 2. The clamp
# ------------

# the first level of xs, else d
def first(xs: List<&2, Lv>, d: Lv) -> Lv:
  match xs:
    case Nil{}:
      d
    case x <> rest:
      x

# the order in which the clamp tries the levels: l and up the ladder,
# then down the ladder from the level below l
def scan(+l: Lv) -> List<&2, Lv>:
  List.append(&2, Lv, List.drop(&2, Lv, ladder(), Lv.idx(l)), List.reverse(&2, Lv, List.take(&2, Lv, ladder(), Lv.idx(l))))

# the head of xs is in lad
def in.at(xs: List<&2, Lv>, +lad: List<&2, Lv>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      has(lad, x)

# the first level of xs in lad, else d; hit is in.at(xs, lad)
def find.go(xs: List<&2, Lv>, +lad: List<&2, Lv>, d: Lv, hit: Bool) -> Lv:
  match xs:
    case Nil{}:
      d
    case +x <> +rest:
      match hit:
        case True{}:
          x
        case False{}:
          find.go(rest, lad, d, in.at(rest, lad))

def clamp.at(b: Bool, +l: Lv, +lad: List<&2, Lv>) -> Lv:
  match b:
    case True{}:
      l
    case False{}:
      find.go(scan(l), lad, first(lad, Off{}), in.at(scan(l), lad))

# the clamp of l to the offered levels lad
def clamp.in(+lad: List<&2, Lv>, +l: Lv) -> Lv:
  clamp.at(has(lad, l), l, lad)

def clamp(+m: Mdl, +l: Lv) -> Lv:
  clamp.in(offered(m), l)

# 3. The cycle
# ------------

type Dir is Data:
  Forward{}
  Backward{}

# xs has at least two levels
def two(xs: List<&2, Lv>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      match rest:
        case Nil{}:
          False{}
        case y <> more:
          True{}

# the last level of xs, else d
def last(xs: List<&2, Lv>, d: Lv) -> Lv:
  match xs:
    case Nil{}:
      d
    case x <> rest:
      last(rest, x)

# the head of xs is c
def at(xs: List<&2, Lv>, +c: Lv) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Lv.eq(x, c)

# the level after the first c of xs, top past the end; None when xs has
# no c; hit is at(xs, c)
def fwd.go(xs: List<&2, Lv>, +c: Lv, top: Lv, hit: Bool) -> Maybe<&2, Lv>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{first(rest, top)}
        case False{}:
          fwd.go(rest, c, top, at(rest, c))

# the level before the first c of xs, prev before the head; None when xs
# has no c; hit is at(xs, c)
def bwd.go(xs: List<&2, Lv>, +c: Lv, prev: Lv, hit: Bool) -> Maybe<&2, Lv>:
  match xs:
    case Nil{}:
      None{}
    case +x <> +rest:
      match hit:
        case True{}:
          Some{prev}
        case False{}:
          bwd.go(rest, c, x, at(rest, c))

# one step from c along lad, wrapping at the ends
def move(d: Dir, +lad: List<&2, Lv>, +c: Lv) -> Maybe<&2, Lv>:
  match d:
    case Forward{}:
      fwd.go(lad, c, first(lad, Off{}), at(lad, c))
    case Backward{}:
      bwd.go(lad, c, last(lad, Off{}), at(lad, c))

def cycle.at(b: Bool, +lad: List<&2, Lv>, +l: Lv, d: Dir) -> Maybe<&2, Lv>:
  match b:
    case True{}:
      move(d, lad, clamp.in(lad, l))
    case False{}:
      None{}

# one cycle step from l along the offered levels lad
def cycle.in(+lad: List<&2, Lv>, +l: Lv, d: Dir) -> Maybe<&2, Lv>:
  cycle.at(two(lad), lad, l, d)

def cycle(+m: Mdl, +l: Lv, d: Dir) -> Maybe<&2, Lv>:
  cycle.in(offered(m), l, d)

# the level after one cycle step: the step's level, else l unchanged
def turn(+m: Mdl, +l: Lv, d: Dir) -> Lv:
  Maybe.default(&2, Lv, cycle(m, l, d), l)

# 4. The session
# --------------

# the session's catalog model (None: not in the catalog) and stored level
# (None: unset)
type Sess is Data:
  Sess{model: Maybe<&2, Mdl>, stored: Maybe<&2, Lv>}

type Act is Data:
  Switch{m: Mdl}    # switch to the catalog model m
  SetLevel{l: Lv}   # set the level l
  Step{d: Dir}      # one cycle step

# What the display shows
type Shown is Data:
  Default{}         # no stored level: the token `default`
  Level{l: Lv}

def Sess.stored(s: Sess) -> Maybe<&2, Lv>:
  match s:
    case Sess{mo, st}:
      st

# l fitted to the catalog model: clamped, unchanged without one
def fit(mo: Maybe<&2, Mdl>, +l: Lv) -> Lv:
  match mo:
    case None{}:
      l
    case Some{m}:
      clamp(m, l)

# open: the stored level, else the default, fitted to the model
def open(s: Sess, dflt: Lv) -> Sess:
  match s:
    case Sess{+mo, st}:
      Sess{mo, Some{fit(mo, Maybe.default(&2, Lv, st, dflt))}}

# the level a cycle step stores: the step's level clamped; l when the
# step changes nothing
def step.set(+m: Mdl, r: Maybe<&2, Lv>, l: Lv) -> Lv:
  match r:
    case None{}:
      l
    case Some{k}:
      clamp(m, k)

def step.lv(mo: Maybe<&2, Mdl>, +l: Lv, d: Dir) -> Lv:
  match mo:
    case None{}:
      l
    case Some{+m}:
      step.set(m, cycle(m, l, d), l)

# an action on a session with stored level l
def act.set(a: Act, +mo: Maybe<&2, Mdl>, +l: Lv) -> Sess:
  match a:
    case Switch{+m}:
      Sess{Some{m}, Some{clamp(m, l)}}
    case SetLevel{k}:
      Sess{mo, Some{fit(mo, k)}}
    case Step{d}:
      Sess{mo, Some{step.lv(mo, l, d)}}

# an action on a session with no stored level
def act.unset(a: Act, +mo: Maybe<&2, Mdl>) -> Sess:
  match a:
    case Switch{m}:
      Sess{Some{m}, None{}}
    case SetLevel{k}:
      Sess{mo, Some{fit(mo, k)}}
    case Step{d}:
      Sess{mo, None{}}

def act(a: Act, s: Sess) -> Sess:
  match s:
    case Sess{mo, st}:
      match st:
        case None{}:
          act.unset(a, mo)
        case Some{l}:
          act.set(a, mo, l)

# the session after the actions
def run(acts: List<&2, Act>, s: Sess) -> Sess:
  match acts:
    case Nil{}:
      s
    case a <> rest:
      run(rest, act(a, s))

# the level the runtime sends: the stored level, else off, fitted
def sent(s: Sess) -> Lv:
  match s:
    case Sess{mo, st}:
      fit(mo, Maybe.default(&2, Lv, st, Off{}))

# the level the display shows
def shown(s: Sess) -> Shown:
  match s:
    case Sess{mo, st}:
      match st:
        case None{}:
          Default{}
        case Some{l}:
          Level{fit(mo, l)}
