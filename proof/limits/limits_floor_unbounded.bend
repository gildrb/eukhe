# eukhe: the proof of LAW limits_floor_unbounded
#
# PROOF: the floor is budget's lack; a dimension without a number asks 0 of 0 there, which fits (lfu.hit), and no other dimension's check names it (lfu.not).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../spec/budget/ledger.bend as SL

# a dimension that fits is not the one named
def lfu.hit(-d: B.Dim, b: Bool, -rest: Maybe<&2, B.Dim>, hb: {b == True{} : Bool}, k: {S.names(d, rest) == False{} : Bool}) -> {S.names(d, B.lack.at(b, d, rest)) == False{} : Bool}:
  match b:
    case True{}:
      k
    case False{}:
      LB.lmb.absurd_ft({S.names(d, B.lack.at(False{}, d, rest)) == False{} : Bool}, hb)

# another dimension's check never names d
def lfu.not(-d: B.Dim, b: Bool, -e: B.Dim, -rest: Maybe<&2, B.Dim>, ne: {S.dim_is(d, e) == False{} : Bool}, k: {S.names(d, rest) == False{} : Bool}) -> {S.names(d, B.lack.at(b, e, rest)) == False{} : Bool}:
  match b:
    case True{}:
      k
    case False{}:
      ne

def lfu.cost(n: B.Ask, f: B.Amt, +now: Nat, +until: Nat, h: {Nat.is_le(SL.at(B.Cost{}, SL.amt(n)), SL.at(B.Cost{}, f)) == True{} : Bool}) -> {S.names(B.Cost{}, B.lack(n, f, now, until)) == False{} : Bool}:
  match n f:
    case B.Ask{B.Amt{+nc, +nk, +nn, +nr}, +nm} B.Amt{+fc, +fk, +fn, +fr}:
      lfu.hit(B.Cost{}, Nat.is_le(nc, fc), B.lack.at(Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})))), h, lfu.not(B.Cost{}, Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}))), {==}, lfu.not(B.Cost{}, Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})), {==}, lfu.not(B.Cost{}, Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}), {==}, lfu.not(B.Cost{}, Nat.is_le(nr, fr), B.Reqs{}, None{}, {==}, {==})))))

def lfu.tok(n: B.Ask, f: B.Amt, +now: Nat, +until: Nat, h: {Nat.is_le(SL.at(B.Tok{}, SL.amt(n)), SL.at(B.Tok{}, f)) == True{} : Bool}) -> {S.names(B.Tok{}, B.lack(n, f, now, until)) == False{} : Bool}:
  match n f:
    case B.Ask{B.Amt{+nc, +nk, +nn, +nr}, +nm} B.Amt{+fc, +fk, +fn, +fr}:
      lfu.not(B.Tok{}, Nat.is_le(nc, fc), B.Cost{}, B.lack.at(Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})))), {==}, lfu.hit(B.Tok{}, Nat.is_le(nk, fk), B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}))), h, lfu.not(B.Tok{}, Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})), {==}, lfu.not(B.Tok{}, Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}), {==}, lfu.not(B.Tok{}, Nat.is_le(nr, fr), B.Reqs{}, None{}, {==}, {==})))))

def lfu.time(n: B.Ask, f: B.Amt, +now: Nat, +until: Nat, h: {Nat.is_le(Nat.add(now, SL.ms(n)), until) == True{} : Bool}) -> {S.names(B.Time{}, B.lack(n, f, now, until)) == False{} : Bool}:
  match n f:
    case B.Ask{B.Amt{+nc, +nk, +nn, +nr}, +nm} B.Amt{+fc, +fk, +fn, +fr}:
      lfu.not(B.Time{}, Nat.is_le(nc, fc), B.Cost{}, B.lack.at(Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})))), {==}, lfu.not(B.Time{}, Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}))), {==}, lfu.hit(B.Time{}, Nat.is_le(Nat.add(now, nm), until), B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})), h, lfu.not(B.Time{}, Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}), {==}, lfu.not(B.Time{}, Nat.is_le(nr, fr), B.Reqs{}, None{}, {==}, {==})))))

def lfu.calls(n: B.Ask, f: B.Amt, +now: Nat, +until: Nat, h: {Nat.is_le(SL.at(B.Calls{}, SL.amt(n)), SL.at(B.Calls{}, f)) == True{} : Bool}) -> {S.names(B.Calls{}, B.lack(n, f, now, until)) == False{} : Bool}:
  match n f:
    case B.Ask{B.Amt{+nc, +nk, +nn, +nr}, +nm} B.Amt{+fc, +fk, +fn, +fr}:
      lfu.not(B.Calls{}, Nat.is_le(nc, fc), B.Cost{}, B.lack.at(Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})))), {==}, lfu.not(B.Calls{}, Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}))), {==}, lfu.not(B.Calls{}, Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})), {==}, lfu.hit(B.Calls{}, Nat.is_le(nn, fn), B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}), h, lfu.not(B.Calls{}, Nat.is_le(nr, fr), B.Reqs{}, None{}, {==}, {==})))))

def lfu.reqs(n: B.Ask, f: B.Amt, +now: Nat, +until: Nat, h: {Nat.is_le(SL.at(B.Reqs{}, SL.amt(n)), SL.at(B.Reqs{}, f)) == True{} : Bool}) -> {S.names(B.Reqs{}, B.lack(n, f, now, until)) == False{} : Bool}:
  match n f:
    case B.Ask{B.Amt{+nc, +nk, +nn, +nr}, +nm} B.Amt{+fc, +fk, +fn, +fr}:
      lfu.not(B.Reqs{}, Nat.is_le(nc, fc), B.Cost{}, B.lack.at(Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})))), {==}, lfu.not(B.Reqs{}, Nat.is_le(nk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}))), {==}, lfu.not(B.Reqs{}, Nat.is_le(Nat.add(now, nm), until), B.Time{}, B.lack.at(Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{})), {==}, lfu.not(B.Reqs{}, Nat.is_le(nn, fn), B.Calls{}, B.lack.at(Nat.is_le(nr, fr), B.Reqs{}, None{}), {==}, lfu.hit(B.Reqs{}, Nat.is_le(nr, fr), None{}, h, {==})))))

def lfu.at(d: B.Dim, +c1: Nat, +c2: Nat, +c3: Nat, +c4: Nat, +cm: Nat, +k1: Nat, +k2: Nat, +k3: Nat, +k4: Nat, +km: Nat, +v1: L.Val, +v2: L.Val, +v3: L.Val, +v4: L.Val, +v5: L.Val, h: {S.is_at(S.dim(d, L.Lims{v1, v2, v3, v4, v5})) == False{} : Bool}) -> {S.names(d, L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}:
  match d:
    case B.Cost{}:
      match v1:
        case L.Unset{}:
          lfu.cost(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{L.Unset{}, v2, v3, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{L.Unset{}, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{L.Unset{}, v2, v3, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{L.Unset{}, v2, v3, v4, v5})), {==})
        case L.Unlimited{}:
          lfu.cost(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{L.Unlimited{}, v2, v3, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{L.Unlimited{}, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{L.Unlimited{}, v2, v3, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{L.Unlimited{}, v2, v3, v4, v5})), {==})
        case L.At{x}:
          LB.lmb.absurd_tf({S.names(B.Cost{}, L.floor(L.Lims{L.At{x}, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}, h)
    case B.Tok{}:
      match v2:
        case L.Unset{}:
          lfu.tok(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, L.Unset{}, v3, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, L.Unset{}, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, L.Unset{}, v3, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, L.Unset{}, v3, v4, v5})), {==})
        case L.Unlimited{}:
          lfu.tok(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, L.Unlimited{}, v3, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, L.Unlimited{}, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, L.Unlimited{}, v3, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, L.Unlimited{}, v3, v4, v5})), {==})
        case L.At{x}:
          LB.lmb.absurd_tf({S.names(B.Tok{}, L.floor(L.Lims{v1, L.At{x}, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}, h)
    case B.Time{}:
      match v3:
        case L.Unset{}:
          lfu.time(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, L.Unset{}, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, L.Unset{}, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, L.Unset{}, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, L.Unset{}, v4, v5})), {==})
        case L.Unlimited{}:
          lfu.time(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, L.Unlimited{}, v4, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, L.Unlimited{}, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, L.Unlimited{}, v4, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, L.Unlimited{}, v4, v5})), {==})
        case L.At{x}:
          LB.lmb.absurd_tf({S.names(B.Time{}, L.floor(L.Lims{v1, v2, L.At{x}, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}, h)
    case B.Calls{}:
      match v4:
        case L.Unset{}:
          lfu.calls(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, v3, L.Unset{}, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, v3, L.Unset{}, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, v3, L.Unset{}, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, v3, L.Unset{}, v5})), {==})
        case L.Unlimited{}:
          lfu.calls(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, v3, L.Unlimited{}, v5}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, v3, L.Unlimited{}, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, v3, L.Unlimited{}, v5}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, v3, L.Unlimited{}, v5})), {==})
        case L.At{x}:
          LB.lmb.absurd_tf({S.names(B.Calls{}, L.floor(L.Lims{v1, v2, v3, L.At{x}, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}, h)
    case B.Reqs{}:
      match v5:
        case L.Unset{}:
          lfu.reqs(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, v3, v4, L.Unset{}}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, v3, v4, L.Unset{}}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, v3, v4, L.Unset{}}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, v3, v4, L.Unset{}})), {==})
        case L.Unlimited{}:
          lfu.reqs(B.need(B.Work{}, B.Ask{B.zero(), 0n}, L.bounded(L.Lims{v1, v2, v3, v4, L.Unlimited{}}, B.Ask{B.Amt{k1, k2, k3, k4}, km}), L.bounded(L.Lims{v1, v2, v3, v4, L.Unlimited{}}, B.Ask{B.Amt{c1, c2, c3, c4}, cm})), L.caps(L.Lims{v1, v2, v3, v4, L.Unlimited{}}), 0n, L.cap(L.Lims.ms(L.Lims{v1, v2, v3, v4, L.Unlimited{}})), {==})
        case L.At{x}:
          LB.lmb.absurd_tf({S.names(B.Reqs{}, L.floor(L.Lims{v1, v2, v3, v4, L.At{x}}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km})) == False{} : Bool}, h)

def Limits.limits_floor_unbounded(l, c, keep, d, h):
  match l c keep:
    case L.Lims{v1, v2, v3, v4, v5} B.Ask{B.Amt{c1, c2, c3, c4}, cm} B.Ask{B.Amt{k1, k2, k3, k4}, km}:
      lfu.at(d, c1, c2, c3, c4, cm, k1, k2, k3, k4, km, v1, v2, v3, v4, v5, h)
