# eukhe: the proof of LAW limits_floor_drops_unbounded
#
# PROOF: the floor reads each dimension through bound and cap; a closed dimension's bound is the asked number kept only where the limits give one, and its cap the number, so each of the fifteen places rewrites to the floor of the limits as given (lfd.k, lfd.n).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S

# a number asked of a dimension counts as the closed dimension keeps it
def lfd.k(v: L.Val, x: Nat) -> {L.bound(v, x) == S.keep_if(S.is_at(v), x) : Nat}:
  match v:
    case L.Unset{}:
      {==}
    case L.At{n}:
      {==}
    case L.Unlimited{}:
      {==}

# a dimension's cap is its number, 0 without one
def lfd.n(v: L.Val) -> {L.cap(v) == S.num(v) : Nat}:
  match v:
    case L.Unset{}:
      {==}
    case L.At{n}:
      {==}
    case L.Unlimited{}:
      {==}

def lfd.at(+v1: L.Val, +v2: L.Val, +v3: L.Val, +v4: L.Val, +v5: L.Val, +c1: Nat, +c2: Nat, +c3: Nat, +c4: Nat, +cm: Nat, +k1: Nat, +k2: Nat, +k3: Nat, +k4: Nat, +km: Nat) -> {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == L.floor(S.closed(L.Lims{v1, v2, v3, v4, v5}), S.only(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}), S.only(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) : Maybe<&2, B.Dim>}:
  %lfd.k(v1, k1) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{_, S.keep_if(S.is_at(v2), k2), S.keep_if(S.is_at(v4), k3), S.keep_if(S.is_at(v5), k4)}, S.keep_if(S.is_at(v3), km)}, B.Ask{B.Amt{S.keep_if(S.is_at(v1), c1), S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v2, k2) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), _, S.keep_if(S.is_at(v4), k3), S.keep_if(S.is_at(v5), k4)}, S.keep_if(S.is_at(v3), km)}, B.Ask{B.Amt{S.keep_if(S.is_at(v1), c1), S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v4, k3) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), _, S.keep_if(S.is_at(v5), k4)}, S.keep_if(S.is_at(v3), km)}, B.Ask{B.Amt{S.keep_if(S.is_at(v1), c1), S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v5, k4) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), _}, S.keep_if(S.is_at(v3), km)}, B.Ask{B.Amt{S.keep_if(S.is_at(v1), c1), S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v3, km) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, _}, B.Ask{B.Amt{S.keep_if(S.is_at(v1), c1), S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v1, c1) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{_, S.keep_if(S.is_at(v2), c2), S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v2, c2) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), _, S.keep_if(S.is_at(v4), c3), S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v4, c3) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), _, S.keep_if(S.is_at(v5), c4)}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v5, c4) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), _}, S.keep_if(S.is_at(v3), cm)}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.k(v3, cm) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, _}), B.Amt{S.num(v1), S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.n(v1) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, L.bound(v3, cm)}), B.Amt{_, S.num(v2), S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.n(v2) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, L.bound(v3, cm)}), B.Amt{L.cap(v1), _, S.num(v4), S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.n(v4) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, L.bound(v3, cm)}), B.Amt{L.cap(v1), L.cap(v2), _, S.num(v5)}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.n(v5) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, L.bound(v3, cm)}), B.Amt{L.cap(v1), L.cap(v2), L.cap(v4), _}, 0n, S.num(v3)) : Maybe<&2, B.Dim>}
  %lfd.n(v3) : {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, B.Ask{B.Amt{L.bound(v1, k1), L.bound(v2, k2), L.bound(v4, k3), L.bound(v5, k4)}, L.bound(v3, km)}, B.Ask{B.Amt{L.bound(v1, c1), L.bound(v2, c2), L.bound(v4, c3), L.bound(v5, c4)}, L.bound(v3, cm)}), B.Amt{L.cap(v1), L.cap(v2), L.cap(v4), L.cap(v5)}, 0n, _) : Maybe<&2, B.Dim>}
  {==}

def Limits.limits_floor_drops_unbounded(l, c, keep):
  match l c keep:
    case L.Lims{v1, v2, v3, v4, v5} B.Ask{B.Amt{c1, c2, c3, c4}, cm} B.Ask{B.Amt{k1, k2, k3, k4}, km}:
      lfd.at(v1, v2, v3, v4, v5, c1, c2, c3, c4, cm, k1, k2, k3, k4, km)
