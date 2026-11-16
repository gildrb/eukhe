# eukhe: lemmas shared by the proofs of area work_list: the positions of
# the open items from i + 1 are those from i, one up; what one up keeps
# (emptiness, membership, order); the entry's encoder of a request is the
# spec's spelling

import Base
import ../../bend/work_list.bend as Wl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_list.bend as S
import ../../laws/work_list.bend as WorkList
import ../log/base.bend as LLog

# Positions
# ---------

# every position one up
def wlb.up(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case x <> t:
      (1n+x) <> wlb.up(t)

# the list is empty
def wlb.nil(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      False{}

# the open items counted from i + 1 are those counted from i, one up
def wlb.shift(done: List<&2, Bool>, +i: Nat) -> {Wl.open(done, 1n+i) == wlb.up(Wl.open(done, i)) : List<&2, Nat>}:
  match done:
    case Nil{}:
      {==}
    case d <> +t:
      match d:
        case True{}:
          wlb.shift(t, 1n+i)
        case False{}:
          %wlb.shift(t, 1n+i) : {(1n+i) <> Wl.open(t, 1n+(1n+i)) == (1n+i) <> _ : List<&2, Nat>}
          {==}

# a hand-back names left exactly its open items
def wlb.left(xs: List<&2, Nat>) -> {S.left(Wl.of_open(xs)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

# a hand-back is finished exactly when no item is open
def wlb.finished(xs: List<&2, Nat>) -> {S.finished(Wl.of_open(xs)) == wlb.nil(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

# one up keeps emptiness
def wlb.nil_up(xs: List<&2, Nat>) -> {wlb.nil(wlb.up(xs)) == wlb.nil(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

# nothing one up is 0
def wlb.member_zero(xs: List<&2, Nat>) -> {S.member(0n, wlb.up(xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      wlb.member_zero(t)

# k + 1 is one up exactly when k is
def wlb.member_up(+k: Nat, xs: List<&2, Nat>) -> {S.member(1n+k, wlb.up(xs)) == S.member(k, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %wlb.member_up(k, t) : {Bool.or(S.same(k, x), S.member(1n+k, wlb.up(t))) == Bool.or(S.same(k, x), _) : Bool}
      {==}

# one up rises from lo + 1 exactly when the list rises from lo
def wlb.rising_up(xs: List<&2, Nat>, +lo: Nat) -> {S.rising(wlb.up(xs), 1n+lo) == S.rising(xs, lo) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %wlb.rising_up(t, 1n+x) : {Bool.and(S.le(lo, x), S.rising(wlb.up(t), 1n+(1n+x))) == Bool.and(S.le(lo, x), _) : Bool}
      {==}

# one up rises from 0 exactly when the list does
def wlb.rising_zero(xs: List<&2, Nat>) -> {S.rising(wlb.up(xs), 0n) == S.rising(xs, 0n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %wlb.rising_up(t, 1n+x) : {S.rising(wlb.up(t), 1n+(1n+x)) == _ : Bool}
      {==}

# Wire
# ----

# the log area's spelling of Bool items is the spec's
def wlb.bools(xs: List<&2, Bool>, rest: String) -> {LLog.pe.bools(xs, rest) == WorkList.sp_w_bools(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, LLog.pe.bools(t, rest), WorkList.sp_w_bools(t, rest), wlb.bools(t, rest)) : {Wr.put_bool(x, _) == Wr.put_bool(x, WorkList.sp_w_bools(t, rest)) : String}
      {==}

# a list of Bools is spelled by the spec
def wlb.put_list(+xs: List<&2, Bool>, rest: String) -> {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), WorkList.sp_w_bools(xs, rest)) : String}:
  %wlb.bools(xs, rest) : {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == Wr.put_nat(List.length(&2, Bool, xs), _) : String}
  LLog.pe.put_list(xs, rest)
