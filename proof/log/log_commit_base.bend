# eukhe: lemmas of the laws of a commit's plan (log_commit_sidecars,
# log_commit_marker_then_ack, log_commit_flushes): what each walk does over
# the sidecars' appends and flushes of a plan, from any index k.
#
# lc.in(k, i, ds): the appends (or flushes) from index k of the sidecars ds
# reach the index i. Before k nothing reaches i (lc.apps_past, lc.fl_past);
# from k the walk of the sidecar i sees its append once (lc.apps) and its
# flush (lc.fl), and the other walks see none of them.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic

# the indexes k, 1 + k, .. of the sidecars ds reach i (recursion on ds
# first, so it shrinks)
def lc.reach(ds: List<&2, Bool>, +k: Nat, +i: Nat) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> more:
      Bool.or(Nat.is_eq(k, i), lc.reach(more, 1n+k, i))

def lc.in(k: Nat, i: Nat, ds: List<&2, Bool>) -> Bool:
  lc.reach(ds, k, i)

# Nat facts
# ---------

def lc.lt_succ(i: Nat, k: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Nat.is_lt(i, 1n+k) == True{} : Bool}:
  match i k:
    case 0n 0n:
      LLogicLogic.wr_absurd({Nat.is_lt(0n, 1n) == True{} : Bool}, h)
    case 0n 1n+m:
      {==}
    case 1n+j 0n:
      LLogicLogic.wr_absurd({Nat.is_lt(1n+j, 1n) == True{} : Bool}, h)
    case 1n+j 1n+m:
      lc.lt_succ(j, m, h)

def lc.lt_ne(i: Nat, k: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Nat.is_eq(k, i) == False{} : Bool}:
  match i k:
    case 0n 0n:
      LLogicLogic.wr_absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+m:
      {==}
    case 1n+j 0n:
      LLogicLogic.wr_absurd({Nat.is_eq(0n, 1n+j) == False{} : Bool}, h)
    case 1n+j 1n+m:
      lc.lt_ne(j, m, h)

def lc.eq_lt(k: Nat, i: Nat, h: {Nat.is_eq(k, i) == True{} : Bool}) -> {Nat.is_lt(i, 1n+k) == True{} : Bool}:
  match k i:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      LLogicLogic.wr_absurd({Nat.is_lt(1n+j, 1n) == True{} : Bool}, h)
    case 1n+m 0n:
      {==}
    case 1n+m 1n+j:
      lc.eq_lt(m, j, h)

def lc.or_f1(a: Bool, b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pf.absurd_tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def lc.or_f2(a: Bool, b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pf.absurd_tf({b == False{} : Bool}, h)
    case False{}:
      h

# The sidecars, per index
# -----------------------

def lc.in_shift(ds: List<&2, Bool>, +k: Nat, +i: Nat) -> {lc.in(1n+k, 1n+i, ds) == lc.in(k, i, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      %lc.in_shift(more, 1n+k, i) : {Bool.or(Nat.is_eq(k, i), lc.in(2n+k, 1n+i, more)) == Bool.or(Nat.is_eq(k, i), _) : Bool}
      {==}

def lc.in_nth(ds: List<&2, Bool>, +i: Nat) -> {lc.in(0n, i, ds) == Maybe.is_some(&2, Bool, Log.log_nth(ds, i)) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      match i:
        case 0n:
          {==}
        case 1n+j:
          %Equal.sym(Bool, lc.in(1n, 1n+j, more), lc.in(0n, j, more), lc.in_shift(more, 0n, j)) : {_ == Maybe.is_some(&2, Bool, Log.log_nth(more, j)) : Bool}
          lc.in_nth(more, j)

def lc.in_none(ds: List<&2, Bool>, +i: Nat, h: {Log.log_nth(ds, i) == None{} : Maybe<&2, Bool>}) -> {lc.in(0n, i, ds) == False{} : Bool}:
  %h : {lc.in(0n, i, ds) == Maybe.is_some(&2, Bool, _) : Bool}
  lc.in_nth(ds, i)

def lc.in_some(ds: List<&2, Bool>, +i: Nat, d: Bool, h: {Log.log_nth(ds, i) == Some{d} : Maybe<&2, Bool>}) -> {lc.in(0n, i, ds) == True{} : Bool}:
  %h : {lc.in(0n, i, ds) == Maybe.is_some(&2, Bool, _) : Bool}
  lc.in_nth(ds, i)

# Unit at Some{True}, A at Some{False}: refutes Some{True} == Some{False}
def lc.SD(m: Maybe<&2, Bool>, A: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      match x:
        case True{}:
          Unit
        case False{}:
          A

def lc.some_tf(-A: Type, e: {Some{True{}} == Some{False{}} : Maybe<&2, Bool>}) -> A:
  %e : lc.SD(_, A)
  Unit{}

# a sidecar whose entry is not durable makes the commit fresh
def lc.fresh_false(ds: List<&2, Bool>, i: Nat, h: {Log.log_nth(ds, i) == Some{False{}} : Maybe<&2, Bool>}) -> {Lr.plan.fresh(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      LLogicLogic.themes.pt.none_some({Lr.plan.fresh(Nil{}) == True{} : Bool}, Bool, False{}, h)
    case x <> more:
      match x:
        case True{}:
          match i:
            case 0n:
              lc.some_tf({Lr.plan.fresh(True{} <> more) == True{} : Bool}, h)
            case 1n+j:
              lc.fresh_false(more, j, h)
        case False{}:
          {==}

def lc.fresh_some(ds: List<&2, Bool>, i: Nat, d: Bool, h: {Log.log_nth(ds, i) == Some{d} : Maybe<&2, Bool>}) -> {Bool.or(d, Lr.plan.fresh(ds)) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      lc.fresh_false(ds, i, h)

# the walk of the sidecar i over the appends from an index past i
def lc.apps_past(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +w: Bool, +f: Bool, +e: Bool, +fs: Bool, +h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Log.log_side_walk(Lr.plan.appends(ds, k, rest), i, w, f, e, fs) == Log.log_side_walk(rest, i, w, f, e, fs) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      +nx = Lr.plan.appends(more, 1n+k, rest)
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, lc.lt_ne(i, k, h)) : {Bool.and(Bool.not(Bool.and(_, w)), Log.log_side_walk(nx, i, Bool.or(_, w), Bool.and(Bool.not(_), f), e, fs)) == Log.log_side_walk(rest, i, w, f, e, fs) : Bool}
      lc.apps_past(more, 1n+k, i, rest, w, f, e, fs, lc.lt_succ(i, k, h))

# one append of the walk of the sidecar i (not appended yet), at the index k
def lc.apps.hit(b: Bool, +more: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +f: Bool, +e: Bool, +fs: Bool, +h: {Nat.is_eq(k, i) == b : Bool}, ih: {Log.log_side_walk(Lr.plan.appends(more, 1n+k, rest), i, False{}, f, e, fs) == Log.log_side_walk(rest, i, lc.in(1n+k, i, more), Bool.and(Bool.not(lc.in(1n+k, i, more)), f), e, fs) : Bool}) -> {Bool.and(Bool.not(Bool.and(Nat.is_eq(k, i), False{})), Log.log_side_walk(Lr.plan.appends(more, 1n+k, rest), i, Bool.or(Nat.is_eq(k, i), False{}), Bool.and(Bool.not(Nat.is_eq(k, i)), f), e, fs)) == Log.log_side_walk(rest, i, Bool.or(Nat.is_eq(k, i), lc.in(1n+k, i, more)), Bool.and(Bool.not(Bool.or(Nat.is_eq(k, i), lc.in(1n+k, i, more))), f), e, fs) : Bool}:
  match b:
    case True{}:
      +nx = Lr.plan.appends(more, 1n+k, rest)
      +r = lc.in(1n+k, i, more)
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, h) : {Bool.and(Bool.not(Bool.and(_, False{})), Log.log_side_walk(nx, i, Bool.or(_, False{}), Bool.and(Bool.not(_), f), e, fs)) == Log.log_side_walk(rest, i, Bool.or(_, r), Bool.and(Bool.not(Bool.or(_, r)), f), e, fs) : Bool}
      lc.apps_past(more, 1n+k, i, rest, True{}, False{}, e, fs, lc.eq_lt(k, i, h))
    case False{}:
      +nx = Lr.plan.appends(more, 1n+k, rest)
      +r = lc.in(1n+k, i, more)
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, h) : {Bool.and(Bool.not(Bool.and(_, False{})), Log.log_side_walk(nx, i, Bool.or(_, False{}), Bool.and(Bool.not(_), f), e, fs)) == Log.log_side_walk(rest, i, Bool.or(_, r), Bool.and(Bool.not(Bool.or(_, r)), f), e, fs) : Bool}
      ih

# the walk of the sidecar i, not appended yet, over the appends from k:
# appended when they reach i
def lc.apps(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +f: Bool, +e: Bool, +fs: Bool) -> {Log.log_side_walk(Lr.plan.appends(ds, k, rest), i, False{}, f, e, fs) == Log.log_side_walk(rest, i, lc.in(k, i, ds), Bool.and(Bool.not(lc.in(k, i, ds)), f), e, fs) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      lc.apps.hit(Nat.is_eq(k, i), more, k, i, rest, f, e, fs, {==}, lc.apps(more, 1n+k, i, rest, f, e, fs))

# the walk of the sidecar i over the flushes from an index past i
def lc.fl_past(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +w: Bool, +f: Bool, +e: Bool, +fs: Bool, +h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Log.log_side_walk(Lr.plan.flushes(ds, k, rest), i, w, f, e, fs) == Log.log_side_walk(rest, i, w, f, e, fs) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      +nx = Lr.plan.flushes(more, 1n+k, rest)
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, lc.lt_ne(i, k, h)) : {Log.log_side_walk(nx, i, w, Bool.or(Bool.and(_, w), Bool.and(Bool.not(_), f)), e, fs) == Log.log_side_walk(rest, i, w, f, e, fs) : Bool}
      lc.fl_past(more, 1n+k, i, rest, w, f, e, fs, lc.lt_succ(i, k, h))

# one flush of the walk of the sidecar i (appended), at the index k
def lc.fl.hit(b: Bool, +more: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +f: Bool, +e: Bool, +fs: Bool, +h: {Nat.is_eq(k, i) == b : Bool}, ih: {Log.log_side_walk(Lr.plan.flushes(more, 1n+k, rest), i, True{}, f, e, fs) == Log.log_side_walk(rest, i, True{}, Bool.or(lc.in(1n+k, i, more), f), e, fs) : Bool}) -> {Log.log_side_walk(Lr.plan.flushes(more, 1n+k, rest), i, True{}, Bool.or(Bool.and(Nat.is_eq(k, i), True{}), Bool.and(Bool.not(Nat.is_eq(k, i)), f)), e, fs) == Log.log_side_walk(rest, i, True{}, Bool.or(Bool.or(Nat.is_eq(k, i), lc.in(1n+k, i, more)), f), e, fs) : Bool}:
  match b:
    case True{}:
      +nx = Lr.plan.flushes(more, 1n+k, rest)
      +r = lc.in(1n+k, i, more)
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, h) : {Log.log_side_walk(nx, i, True{}, Bool.or(Bool.and(_, True{}), Bool.and(Bool.not(_), f)), e, fs) == Log.log_side_walk(rest, i, True{}, Bool.or(Bool.or(_, r), f), e, fs) : Bool}
      lc.fl_past(more, 1n+k, i, rest, True{}, True{}, e, fs, lc.eq_lt(k, i, h))
    case False{}:
      +nx = Lr.plan.flushes(more, 1n+k, rest)
      +r = lc.in(1n+k, i, more)
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, h) : {Log.log_side_walk(nx, i, True{}, Bool.or(Bool.and(_, True{}), Bool.and(Bool.not(_), f)), e, fs) == Log.log_side_walk(rest, i, True{}, Bool.or(Bool.or(_, r), f), e, fs) : Bool}
      ih

# the walk of the sidecar i, appended, over the flushes from k: flushed
# when they reach i
def lc.fl(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +f: Bool, +e: Bool, +fs: Bool) -> {Log.log_side_walk(Lr.plan.flushes(ds, k, rest), i, True{}, f, e, fs) == Log.log_side_walk(rest, i, True{}, Bool.or(lc.in(k, i, ds), f), e, fs) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      lc.fl.hit(Nat.is_eq(k, i), more, k, i, rest, f, e, fs, {==}, lc.fl(more, 1n+k, i, rest, f, e, fs))

# the appends and flushes from k never touch an index they do not reach
def lc.none_apps(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +h: {lc.in(k, i, ds) == False{} : Bool}) -> {Log.log_side_none(Lr.plan.appends(ds, k, rest), i) == Log.log_side_none(rest, i) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, lc.or_f1(Nat.is_eq(k, i), lc.in(1n+k, i, more), h)) : {Bool.and(Bool.not(_), Log.log_side_none(Lr.plan.appends(more, 1n+k, rest), i)) == Log.log_side_none(rest, i) : Bool}
      lc.none_apps(more, 1n+k, i, rest, lc.or_f2(Nat.is_eq(k, i), lc.in(1n+k, i, more), h))

def lc.none_fls(ds: List<&2, Bool>, +k: Nat, +i: Nat, +rest: List<&2, Lr.Act>, +h: {lc.in(k, i, ds) == False{} : Bool}) -> {Log.log_side_none(Lr.plan.flushes(ds, k, rest), i) == Log.log_side_none(rest, i) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, lc.or_f1(Nat.is_eq(k, i), lc.in(1n+k, i, more), h)) : {Bool.and(Bool.not(_), Log.log_side_none(Lr.plan.flushes(more, 1n+k, rest), i)) == Log.log_side_none(rest, i) : Bool}
      lc.none_fls(more, 1n+k, i, rest, lc.or_f2(Nat.is_eq(k, i), lc.in(1n+k, i, more), h))

def lc.none_dir(b: Bool, +rest: List<&2, Lr.Act>, +i: Nat) -> {Log.log_side_none(Lr.plan.dir(b, rest), i) == Log.log_side_none(rest, i) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the steps of an fsync commit from its marker on
def lc.aft(+main: Bool, stamp: Bool) -> List<&2, Lr.Act>:
  Lr.AppendMain{} <> Lr.FlushMain{} <> Lr.plan.dir(Bool.not(main), Lr.plan.stamp(Bool.and(stamp, Bool.not(main)), [Lr.Ack{}]))

def lc.none_aft(main: Bool, stamp: Bool, +i: Nat) -> {Log.log_side_none(lc.aft(main, stamp), i) == True{} : Bool}:
  match main stamp:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the sidecar i, appended and flushed, reaches the marker ready: its entry
# was durable, or the commit is fresh and flushes the directory
def lc.dir_some(b: Bool, +d: Bool, main: Bool, stamp: Bool, +i: Nat, hb: {Bool.or(d, b) == True{} : Bool}) -> {Log.log_side_walk(Lr.plan.dir(b, lc.aft(main, stamp)), i, True{}, True{}, d, True{}) == True{} : Bool}:
  match b:
    case True{}:
      match d:
        case True{}:
          lc.none_aft(main, stamp, i)
        case False{}:
          lc.none_aft(main, stamp, i)
    case False{}:
      match d:
        case True{}:
          lc.none_aft(main, stamp, i)
        case False{}:
          LLogicLogic.wr_absurd({Log.log_side_walk(lc.aft(main, stamp), i, True{}, True{}, False{}, True{}) == True{} : Bool}, hb)

# The main walk
# -------------

def lc.mw_apps(ds: List<&2, Bool>, +k: Nat, +rest: List<&2, Lr.Act>, +m: Bool, +fl: Bool, +e: Bool, +st: Bool, +fs: Bool, +sp: Bool, +was: Bool) -> {Log.log_main_walk(Lr.plan.appends(ds, k, rest), m, fl, e, st, fs, sp, was) == Log.log_main_walk(rest, m, fl, e, st, fs, sp, was) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      lc.mw_apps(more, 1n+k, rest, m, fl, e, st, fs, sp, was)

def lc.mw_fls(ds: List<&2, Bool>, +k: Nat, +rest: List<&2, Lr.Act>, +m: Bool, +fl: Bool, +e: Bool, +st: Bool, +fs: Bool, +sp: Bool, +was: Bool) -> {Log.log_main_walk(Lr.plan.flushes(ds, k, rest), m, fl, e, st, fs, sp, was) == Log.log_main_walk(rest, m, fl, e, st, fs, sp, was) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      lc.mw_fls(more, 1n+k, rest, m, fl, e, st, fs, sp, was)

def lc.mw_tail(b: Bool, main: Bool, stamp: Bool) -> {Log.log_main_walk(Lr.plan.dir(b, lc.aft(main, stamp)), False{}, False{}, main, False{}, True{}, stamp, main) == True{} : Bool}:
  match b main stamp:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# The flush count
# ---------------

def lc.cnt_apps(ds: List<&2, Bool>, +k: Nat, +rest: List<&2, Lr.Act>) -> {Log.log_flush_count(Lr.plan.appends(ds, k, rest)) == Log.log_flush_count(rest) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      lc.cnt_apps(more, 1n+k, rest)

def lc.cnt_fls(ds: List<&2, Bool>, +k: Nat, +rest: List<&2, Lr.Act>) -> {Log.log_flush_count(Lr.plan.flushes(ds, k, rest)) == Nat.add(List.length(&2, Bool, ds), Log.log_flush_count(rest)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +more:
      %lc.cnt_fls(more, 1n+k, rest) : {1n+Log.log_flush_count(Lr.plan.flushes(more, 1n+k, rest)) == 1n+_ : Nat}
      {==}

def lc.cnt_tail(b: Bool, main: Bool, stamp: Bool) -> {Log.log_flush_count(Lr.plan.dir(b, lc.aft(main, stamp))) == Nat.add(Log.log_bit(b), 1n+Log.log_bit(Bool.not(main))) : Nat}:
  match b main stamp:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def lc.fresh(ds: List<&2, Bool>) -> {Lr.plan.fresh(ds) == Log.log_fresh(ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> more:
      match d:
        case True{}:
          lc.fresh(more)
        case False{}:
          {==}
