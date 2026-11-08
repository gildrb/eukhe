# eukhe: lemmas of the poll laws of area wait_any: the code's first
# settled index past targets none of which counts as settled; no index
# when none counts; the code's live test is "some target runs"

import Base
import ../../../bend/wait_any.bend as Wa
import ../../../spec/durable/wait_any.bend as WaSpec
import ../../base/staging.bend as LStg
import ../base.bend as LW

# the code's settled test is the spec's counts (S1)
def wap.settled_eq(+named: Bool, t: Wa.Tgt) -> {Wa.settled(named, t) == WaSpec.counts(named, t) : Bool}:
  match t:
    case Wa.Runs{}:
      {==}
    case Wa.Unread{}:
      {==}
    case Wa.Read{}:
      {==}

# one more unsettled target before: the index moves one further
def wap.later(+named: Bool, +rest: List<&2, Wa.Tgt>, +t: Wa.Tgt, +post: List<&2, Wa.Tgt>, +i: Nat,
  ih: {Wa.first(List.append(&2, Wa.Tgt, rest, Con{t, post}), named, 1n+i) == Some{Nat.add(1n+i, List.length(&2, Wa.Tgt, rest))} : Maybe<&2, Nat>})
  -> {Wa.first(List.append(&2, Wa.Tgt, rest, Con{t, post}), named, 1n+i) == Some{Nat.add(i, 1n+List.length(&2, Wa.Tgt, rest))} : Maybe<&2, Nat>}:
  %Equal.sym(Nat, Nat.add(i, 1n+List.length(&2, Wa.Tgt, rest)), 1n+Nat.add(i, List.length(&2, Wa.Tgt, rest)), LW.wa.add_succ_r(i, List.length(&2, Wa.Tgt, rest))) : {Wa.first(List.append(&2, Wa.Tgt, rest, Con{t, post}), named, 1n+i) == Some{_} : Maybe<&2, Nat>}
  ih

# past pre, none of which counts as settled, the first settled target t
# is at index i + |pre|
def wap.first(pre: List<&2, Wa.Tgt>, +named: Bool, +t: Wa.Tgt, +post: List<&2, Wa.Tgt>, +i: Nat,
  none: {WaSpec.none_settled(named, pre) == True{} : Bool},
  here: {WaSpec.counts(named, t) == True{} : Bool})
  -> {Wa.first(List.append(&2, Wa.Tgt, pre, Con{t, post}), named, i) == Some{Nat.add(i, List.length(&2, Wa.Tgt, pre))} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Wa.settled(named, t), True{}, Equal.trans(Bool, Wa.settled(named, t), WaSpec.counts(named, t), True{}, wap.settled_eq(named, t), here)) : {Wa.first.pick(_, i, Wa.first(post, named, 1n+i)) == Some{Nat.add(i, 0n)} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, LW.wa.add_zero_r(i)))
    case Con{x, +rest}:
      match x:
        case Wa.Runs{}:
          wap.later(named, rest, t, post, i, wap.first(rest, named, t, post, 1n+i, none, here))
        case Wa.Unread{}:
          LStg.stg.absurdF({Wa.first(List.append(&2, Wa.Tgt, Con{Wa.Unread{}, rest}, Con{t, post}), named, i) == Some{Nat.add(i, List.length(&2, Wa.Tgt, Con{Wa.Unread{}, rest}))} : Maybe<&2, Nat>}, none)
        case Wa.Read{}:
          match named:
            case True{}:
              LStg.stg.absurdF({Wa.first(List.append(&2, Wa.Tgt, Con{Wa.Read{}, rest}, Con{t, post}), True{}, i) == Some{Nat.add(i, List.length(&2, Wa.Tgt, Con{Wa.Read{}, rest}))} : Maybe<&2, Nat>}, none)
            case False{}:
              wap.later(False{}, rest, t, post, i, wap.first(rest, False{}, t, post, 1n+i, none, here))

# no target counts as settled: no index
def wap.none_first(ts: List<&2, Wa.Tgt>, +named: Bool, +i: Nat, none: {WaSpec.none_settled(named, ts) == True{} : Bool}) -> {Wa.first(ts, named, i) == None{} : Maybe<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Wa.Runs{}:
          wap.none_first(rest, named, 1n+i, none)
        case Wa.Unread{}:
          LStg.stg.absurdF({Wa.first(Con{Wa.Unread{}, rest}, named, i) == None{} : Maybe<&2, Nat>}, none)
        case Wa.Read{}:
          match named:
            case True{}:
              LStg.stg.absurdF({Wa.first(Con{Wa.Read{}, rest}, True{}, i) == None{} : Maybe<&2, Nat>}, none)
            case False{}:
              wap.none_first(rest, False{}, 1n+i, none)

# the code's live test is the spec's some_runs (S2)
def wap.live_runs(ts: List<&2, Wa.Tgt>) -> {Wa.live(ts) == WaSpec.some_runs(ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Wa.Runs{}:
          {==}
        case Wa.Unread{}:
          wap.live_runs(rest)
        case Wa.Read{}:
          wap.live_runs(rest)

# with no settled target, a poll is the code's last step on whether a
# target runs (r)
def wap.unsettled(+named: Bool, c: Bool, l: Bool, +ts: List<&2, Wa.Tgt>, -r: Bool,
  nf: {Wa.first(ts, named, 0n) == None{} : Maybe<&2, Nat>},
  lv: {Wa.live(ts) == r : Bool})
  -> {Wa.poll(named, c, l, ts) == Wa.poll.none(r, c, l) : Wa.Pick}:
  %Equal.sym(Maybe<&2, Nat>, Wa.first(ts, named, 0n), None{}, nf) : {Wa.poll.found(_, Wa.live(ts), c, l) == Wa.poll.none(r, c, l) : Wa.Pick}
  %Equal.sym(Bool, Wa.live(ts), r, lv) : {Wa.poll.found(None{}, _, c, l) == Wa.poll.none(r, c, l) : Wa.Pick}
  {==}
