# autoresearch (spec): the kept runs of a segment, what it means for a
# metric to beat them, and the segment's best as a property: a kept run's
# metric that no kept run of the segment (not flagged) is better than.
# The order of metrics is a parameter (`~cmp`): the laws of area
# autoresearch (laws/autoresearch.bend) pass the shipped order, which
# metric_order_exact pins to the arithmetic of ./decimal.bend. A spec: the
# shipped code never calls it.

import Base
import ../../bend/autoresearch/dec.bend as D
import ../../bend/autoresearch/state.bend as S

def kept.st(here: Bool, st: Maybe<&2, S.Status>, m: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match here:
    case False{}:
      None{}
    case True{}:
      match st:
        case None{}:
          None{}
        case Some{S.Keep{}}:
          m
        case Some{S.Discard{}}:
          None{}
        case Some{S.Crash{}}:
          None{}
        case Some{S.Checks{}}:
          None{}

# the metric of r when it is a kept run of segment seg that is not flagged
def kept(r: S.Row, +seg: Nat) -> Maybe<&2, D.Dec>:
  match r:
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      match fl:
        case True{}:
          None{}
        case False{}:
          kept.st(Nat.is_eq(sg, seg), st, m)

# a is better than b in direction dir, by the order cmp
def is_better(~cmp: D.Dec -> D.Dec -> Cmp, dir: S.Dir, a: D.Dec, b: D.Dec) -> Bool:
  match dir:
    case S.Lower{}:
      Cmp.is_lt(cmp(a, b))
    case S.Higher{}:
      Cmp.is_gt(cmp(a, b))

def beaten.at(~cmp: D.Dec -> D.Dec -> Cmp, +dir: S.Dir, +m: D.Dec, k: Maybe<&2, D.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      is_better(~cmp, dir, m, x)

# m is better than every kept metric of the segment
def all_beaten(~cmp: D.Dec -> D.Dec -> Cmp, +dir: S.Dir, +m: D.Dec, rs: List<&2, S.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(beaten.at(~cmp, dir, m, kept(r, seg)), all_beaten(~cmp, dir, m, t, seg))

def unbeaten.at(~cmp: D.Dec -> D.Dec -> Cmp, +dir: S.Dir, +b: D.Dec, k: Maybe<&2, D.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      Bool.not(is_better(~cmp, dir, x, b))

# no kept metric of the segment is better than b
def none_better(~cmp: D.Dec -> D.Dec -> Cmp, +dir: S.Dir, +b: D.Dec, rs: List<&2, S.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(unbeaten.at(~cmp, dir, b, kept(r, seg)), none_better(~cmp, dir, b, t, seg))

def ds_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> v:
      False{}
    case x <> u Nil{}:
      False{}
    case x <> u y <> v:
      Bool.and(Nat.is_eq(x, y), ds_eq(u, v))

# a and b are the same decimal
def dec_eq(a: D.Dec, b: D.Dec) -> Bool:
  match a b:
    case D.Dec{na, da, sa} D.Dec{nb, db, sb}:
      Bool.and(Bool.not(Bool.xor(na, nb)), Bool.and(ds_eq(da, db), Nat.is_eq(sa, sb)))

def has.at(+b: D.Dec, k: Maybe<&2, D.Dec>) -> Bool:
  match k:
    case None{}:
      False{}
    case Some{x}:
      dec_eq(x, b)

# b is the metric of a kept run of the segment
def has_kept(+b: D.Dec, rs: List<&2, S.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(has.at(b, kept(r, seg)), has_kept(b, t, seg))

def none.at(k: Maybe<&2, D.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      False{}

# the segment kept no run (that is not flagged)
def none_kept(rs: List<&2, S.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(none.at(kept(r, seg)), none_kept(t, seg))

# b is the segment's best: none when it kept no run; else a kept run's
# metric no kept run is better than
def Best(~cmp: D.Dec -> D.Dec -> Cmp, +dir: S.Dir, b: Maybe<&2, D.Dec>, +rs: List<&2, S.Row>, +seg: Nat) -> Type:
  match b:
    case None{}:
      {none_kept(rs, seg) == True{} : Bool}
    case Some{+x}:
      {has_kept(x, rs, seg) == True{} : Bool} & {none_better(~cmp, dir, x, rs, seg) == True{} : Bool}

def first_kept.or(k: Maybe<&2, D.Dec>, later: Maybe<&2, D.Dec>) -> Maybe<&2, D.Dec>:
  match k:
    case None{}:
      later
    case Some{x}:
      Some{x}

# the segment's baseline: the metric of its first (oldest) kept run that
# is not flagged, rows read oldest first; none when the segment kept no
# such run. Rows of other segments never count.
def first_kept(rs: List<&2, S.Row>, +seg: Nat) -> Maybe<&2, D.Dec>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      first_kept.or(kept(r, seg), first_kept(t, seg))

def logged_count.at(here: Bool, st: Maybe<&2, S.Status>, rest: Nat) -> Nat:
  match here:
    case False{}:
      rest
    case True{}:
      match st:
        case None{}:
          rest
        case Some{k}:
          1n+rest

# how many runs of segment seg were logged (they have a status: keep,
# discard, crash or checks_failed; abandoned rows have none), flagged ones
# included (they still count toward max_iterations). Rows of other
# segments never count.
def logged_count(rs: List<&2, S.Row>, +seg: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc} <> t:
      logged_count.at(Nat.is_eq(sg, seg), st, logged_count(t, seg))
