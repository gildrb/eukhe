# eukhe: the proof of LAW limits_notice_tells
#
# PROOF: the code counts the place up as it goes, the spec shifts on the way back (lnt.go); its membership test is the spec's (lnt.has).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

# the places xs, each i on
def lnt.by(+i: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Nat.add(i, x) <> lnt.by(i, t)

def lnt.by_shift(+i: Nat, xs: List<&2, Nat>) -> {lnt.by(1n+i, xs) == lnt.by(i, S.shift(xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat, Nat.add(i, 1n+x), 1n+Nat.add(i, x), LB.lmb.add_succ(i, x)) : {(1n+Nat.add(i, x)) <> lnt.by(1n+i, t) == _ <> lnt.by(i, S.shift(t)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, lnt.by(1n+i, t), lnt.by(i, S.shift(t)), lnt.by_shift(i, t)) : {(1n+Nat.add(i, x)) <> _ == (1n+Nat.add(i, x)) <> lnt.by(i, S.shift(t)) : List<&2, Nat>}
      {==}

def lnt.by0(xs: List<&2, Nat>) -> {lnt.by(0n, xs) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %Equal.sym(List<&2, Nat>, lnt.by(0n, t), t, lnt.by0(t)) : {x <> _ == x <> t : List<&2, Nat>}
      {==}

# the code's text equality is the spec's
def lnt.same(a: String, b: String) -> {L.same(a, b) == S.same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{Chr{p}, u} SCon{Chr{q}, v}:
      %Equal.sym(Bool, L.same(u, v), S.same(u, v), lnt.same(u, v)) : {L.same.chr(p, q, _) == Bool.and(U32.is_eq(p, q), S.same(u, v)) : Bool}
      {==}

def lnt.has_or(a: Bool, b: Bool) -> {L.has.or(a, b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's membership is the spec's
def lnt.has(+s: String, ls: List<&2, String>) -> {L.has(s, ls) == S.among(s, ls) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, L.has(s, t), S.among(s, t), lnt.has(s, t)) : {L.has.or(L.same(s, h), _) == Bool.or(S.same(s, h), S.among(s, t)) : Bool}
      %Equal.sym(Bool, L.same(s, h), S.same(s, h), lnt.same(s, h)) : {L.has.or(_, S.among(s, t)) == Bool.or(S.same(s, h), S.among(s, t)) : Bool}
      lnt.has_or(S.same(s, h), S.among(s, t))

def lnt.step(b: Bool, +i: Nat, +f: List<&2, Nat>) -> {L.notice.add(b, i, lnt.by(1n+i, f)) == lnt.by(i, S.fresh.at(b, S.shift(f))) : List<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, Nat.add(i, 0n), i, LB.lmb.add_zero(i)) : {i <> lnt.by(1n+i, f) == _ <> lnt.by(i, S.shift(f)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, lnt.by(1n+i, f), lnt.by(i, S.shift(f)), lnt.by_shift(i, f)) : {i <> _ == i <> lnt.by(i, S.shift(f)) : List<&2, Nat>}
      {==}
    case False{}:
      lnt.by_shift(i, f)

def lnt.go(ws: List<&2, L.Win>, +line: Nat, +i: Nat, +told: List<&2, String>) -> {L.notice.now(ws, line, i, told) == lnt.by(i, S.fresh(ws, line, told)) : List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{L.Win{+l, +u}, +t}:
      %Equal.sym(List<&2, Nat>, L.notice.now(t, line, 1n+i, told), lnt.by(1n+i, S.fresh(t, line, told)), lnt.go(t, line, 1n+i, told)) : {L.notice.add(Bool.and(Nat.is_le(line, u), Bool.not(L.has(l, told))), i, _) == lnt.by(i, S.fresh.at(Bool.and(Nat.is_le(line, u), Bool.not(S.among(l, told))), S.shift(S.fresh(t, line, told)))) : List<&2, Nat>}
      %Equal.sym(Bool, L.has(l, told), S.among(l, told), lnt.has(l, told)) : {L.notice.add(Bool.and(Nat.is_le(line, u), Bool.not(_)), i, lnt.by(1n+i, S.fresh(t, line, told))) == lnt.by(i, S.fresh.at(Bool.and(Nat.is_le(line, u), Bool.not(S.among(l, told))), S.shift(S.fresh(t, line, told)))) : List<&2, Nat>}
      lnt.step(Bool.and(Nat.is_le(line, u), Bool.not(S.among(l, told))), i, S.fresh(t, line, told))

def Limits.limits_notice_tells(ws, r, told):
  Equal.trans(List<&2, Nat>, L.notice.now(ws, Nat.sub(1000n, r), 0n, told), lnt.by(0n, S.fresh(ws, Nat.sub(1000n, r), told)), S.fresh(ws, Nat.sub(1000n, r), told), lnt.go(ws, Nat.sub(1000n, r), 0n, told), lnt.by0(S.fresh(ws, Nat.sub(1000n, r), told)))
