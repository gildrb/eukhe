# eukhe: the proof of LAW limits_notice_told
#
# PROOF: the labels told of after are those at or past the line, then those
# told of that no window has, each once (membership survives notice.once:
# lnd.once; membership in an append: lnd.app); a label is at or past the
# line exactly when a window of it is (lnd.over); a told label stays
# exactly when no window has it, the spec's text equality being equality
# (lnd.keep, lnd.eq); a window of a label is at or past the line or below
# it (lnd.labels).

import Base
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ./limits_notice_tells.bend as PNoticeTells
import ../autoresearch/base/line.bend as ALine

# texts the spec calls the same are equal
def lnd.eq(+a: String, +b: String, e: {S.same(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      LB.lmb.absurd_ft({SNil{} == SCon{y, v} : String}, e)
    case SCon{x, u} SNil{}:
      LB.lmb.absurd_ft({SCon{x, u} == SNil{} : String}, e)
    case SCon{Chr{+p}, +u} SCon{Chr{+q}, +v}:
      +h0 = e
      +ep = ALine.al.eq_sound(p, q, LB.lmb.and_l(U32.is_eq(p, q), S.same(u, v), h0))
      +ev = lnd.eq(u, v, LB.lmb.and_r(U32.is_eq(p, q), S.same(u, v), h0))
      %ep : {SCon{Chr{p}, u} == SCon{Chr{_}, v} : String}
      %ev : {SCon{Chr{p}, u} == SCon{Chr{p}, _} : String}
      {==}

def lnd.or3(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# membership in an append is membership in either part
def lnd.app(+s: String, a: List<&2, String>, +b: List<&2, String>) -> {S.among(s, List.append(&2, String, a, b)) == Bool.or(S.among(s, a), S.among(s, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, S.among(s, List.append(&2, String, t, b)), Bool.or(S.among(s, t), S.among(s, b)), lnd.app(s, t, b)) : {Bool.or(S.same(s, h), _) == Bool.or(Bool.or(S.same(s, h), S.among(s, t)), S.among(s, b)) : Bool}
      lnd.or3(S.same(s, h), S.among(s, t), S.among(s, b))

def lnd.or_t(a: Bool, -z: Bool) -> {Bool.or(a, z) == Bool.or(Bool.and(a, True{}), z) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def lnd.or_f(a: Bool, -z: Bool) -> {z == Bool.or(Bool.and(a, False{}), z) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a label added when its window is at or past the line
def lnd.label(+s: String, b: Bool, +l: String, -x: List<&2, String>, -y: Bool, e: {S.among(s, x) == y : Bool}) -> {S.among(s, L.notice.label(b, l, x)) == Bool.or(Bool.and(S.same(s, l), b), y) : Bool}:
  match b:
    case True{}:
      %e : {Bool.or(S.same(s, l), S.among(s, x)) == Bool.or(Bool.and(S.same(s, l), True{}), _) : Bool}
      lnd.or_t(S.same(s, l), S.among(s, x))
    case False{}:
      %e : {S.among(s, x) == Bool.or(Bool.and(S.same(s, l), False{}), _) : Bool}
      lnd.or_f(S.same(s, l), S.among(s, x))

# the labels at or past the line are those of the windows reached
def lnd.over(+s: String, ws: List<&2, L.Win>, +line: Nat) -> {S.among(s, L.notice.over(ws, line)) == S.reached(s, ws, line) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{L.Win{+l, +u}, +t}:
      lnd.label(s, Nat.is_le(line, u), l, L.notice.over(t, line), S.reached(s, t, line), lnd.over(s, t, line))

def lnd.not_le(t: Nat, a: Nat) -> {Nat.is_lt(a, t) == Bool.not(Nat.is_le(t, a)) : Bool}:
  match t a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lnd.not_le(p, q)

def lnd.split(a: Bool, b: Bool, -z: Bool) -> {Bool.or(a, z) == Bool.or(Bool.or(Bool.and(a, b), Bool.and(a, Bool.not(b))), z) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def lnd.or_true(c: Bool) -> {True{} == Bool.or(c, True{}) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def lnd.or_mid(b: Bool, c: Bool, -d: Bool) -> {Bool.or(b, Bool.or(c, d)) == Bool.or(c, Bool.or(b, d)) : Bool}:
  match b:
    case True{}:
      lnd.or_true(c)
    case False{}:
      {==}

def lnd.or_split(a: Bool, b: Bool, c: Bool, -d: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(c, d)) == Bool.or(Bool.or(a, c), Bool.or(b, d)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      lnd.or_mid(b, c, d)

# a label of the windows is reached or below the line
def lnd.labels(+s: String, ws: List<&2, L.Win>, +line: Nat) -> {S.among(s, S.labels(ws)) == Bool.or(S.reached(s, ws, line), S.below(s, ws, line)) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{L.Win{+l, +u}, +t}:
      %Equal.sym(Bool, S.among(s, S.labels(t)), Bool.or(S.reached(s, t, line), S.below(s, t, line)), lnd.labels(s, t, line)) : {Bool.or(S.same(s, l), _) == Bool.or(Bool.or(Bool.and(S.same(s, l), Nat.is_le(line, u)), S.reached(s, t, line)), Bool.or(Bool.and(S.same(s, l), Nat.is_lt(u, line)), S.below(s, t, line))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(u, line), Bool.not(Nat.is_le(line, u)), lnd.not_le(line, u)) : {Bool.or(S.same(s, l), Bool.or(S.reached(s, t, line), S.below(s, t, line))) == Bool.or(Bool.or(Bool.and(S.same(s, l), Nat.is_le(line, u)), S.reached(s, t, line)), Bool.or(Bool.and(S.same(s, l), _), S.below(s, t, line))) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.or(Bool.and(S.same(s, l), Nat.is_le(line, u)), S.reached(s, t, line)), Bool.or(Bool.and(S.same(s, l), Bool.not(Nat.is_le(line, u))), S.below(s, t, line))), Bool.or(Bool.or(Bool.and(S.same(s, l), Nat.is_le(line, u)), Bool.and(S.same(s, l), Bool.not(Nat.is_le(line, u)))), Bool.or(S.reached(s, t, line), S.below(s, t, line))), lnd.or_split(Bool.and(S.same(s, l), Nat.is_le(line, u)), S.reached(s, t, line), Bool.and(S.same(s, l), Bool.not(Nat.is_le(line, u))), S.below(s, t, line))) : {Bool.or(S.same(s, l), Bool.or(S.reached(s, t, line), S.below(s, t, line))) == _ : Bool}
      lnd.split(S.same(s, l), Nat.is_le(line, u), Bool.or(S.reached(s, t, line), S.below(s, t, line)))

def lnd.absorb(a: Bool, t: Bool) -> {Bool.or(Bool.not(a), Bool.and(t, Bool.not(a))) == Bool.not(a) : Bool}:
  match a t:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a told label of the same text as s stands or falls with s
def lnd.keep_at(q: Bool, +s: String, +h: String, +ls: List<&2, String>, +t: List<&2, String>, eq: {S.same(s, h) == q : Bool}) -> {Bool.or(Bool.and(q, Bool.not(S.among(h, ls))), Bool.and(S.among(s, t), Bool.not(S.among(s, ls)))) == Bool.and(Bool.or(q, S.among(s, t)), Bool.not(S.among(s, ls))) : Bool}:
  match q:
    case True{}:
      +e = lnd.eq(s, h, eq)
      %e : {Bool.or(Bool.not(S.among(_, ls)), Bool.and(S.among(s, t), Bool.not(S.among(s, ls)))) == Bool.not(S.among(s, ls)) : Bool}
      lnd.absorb(S.among(s, ls), S.among(s, t))
    case False{}:
      {==}

# a told label stays when no window has it
def lnd.keep(+s: String, told: List<&2, String>, +ls: List<&2, String>) -> {S.among(s, L.notice.keep(told, ls)) == Bool.and(S.among(s, told), Bool.not(S.among(s, ls))) : Bool}:
  match told:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, S.among(s, L.notice.label(Bool.not(L.has(h, ls)), h, L.notice.keep(t, ls))), Bool.or(Bool.and(S.same(s, h), Bool.not(L.has(h, ls))), Bool.and(S.among(s, t), Bool.not(S.among(s, ls)))), lnd.label(s, Bool.not(L.has(h, ls)), h, L.notice.keep(t, ls), Bool.and(S.among(s, t), Bool.not(S.among(s, ls))), lnd.keep(s, t, ls))) : {_ == Bool.and(Bool.or(S.same(s, h), S.among(s, t)), Bool.not(S.among(s, ls))) : Bool}
      %Equal.sym(Bool, L.has(h, ls), S.among(h, ls), PNoticeTells.lnt.has(h, ls)) : {Bool.or(Bool.and(S.same(s, h), Bool.not(_)), Bool.and(S.among(s, t), Bool.not(S.among(s, ls)))) == Bool.and(Bool.or(S.same(s, h), S.among(s, t)), Bool.not(S.among(s, ls))) : Bool}
      lnd.keep_at(S.same(s, h), s, h, ls, t, {==})

# the code's labels are the spec's
def lnd.lbl(ws: List<&2, L.Win>) -> {L.notice.labels(ws) == S.labels(ws) : List<&2, String>}:
  match ws:
    case Nil{}:
      {==}
    case Con{L.Win{l, u}, t}:
      %Equal.sym(List<&2, String>, L.notice.labels(t), S.labels(t), lnd.lbl(t)) : {l <> _ == l <> S.labels(t) : List<&2, String>}
      {==}

def lnd.final(r: Bool, t: Bool, b: Bool) -> {Bool.or(r, Bool.and(t, Bool.not(Bool.or(r, b)))) == Bool.or(r, Bool.and(t, Bool.not(b))) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

# s is in t when it has the text of h and h is in t
def lnd.once_at(q: Bool, +s: String, +h: String, +t: List<&2, String>, eq: {S.same(s, h) == q : Bool}, ht: {S.among(h, t) == True{} : Bool}) -> {S.among(s, t) == Bool.or(q, S.among(s, t)) : Bool}:
  match q:
    case True{}:
      +e = lnd.eq(s, h, eq)
      %Equal.sym(String, s, h, e) : {S.among(_, t) == True{} : Bool}
      ht
    case False{}:
      {==}

# a label kept before the rest made once
def lnd.once_lbl(b: Bool, +s: String, +h: String, +t: List<&2, String>, eb: {L.has(h, t) == b : Bool}, ih: {S.among(s, L.notice.once(t)) == S.among(s, t) : Bool}) -> {S.among(s, L.notice.label(Bool.not(b), h, L.notice.once(t))) == Bool.or(S.same(s, h), S.among(s, t)) : Bool}:
  match b:
    case True{}:
      +ht = Equal.trans(Bool, S.among(h, t), L.has(h, t), True{}, Equal.sym(Bool, L.has(h, t), S.among(h, t), PNoticeTells.lnt.has(h, t)), eb)
      Equal.trans(Bool, S.among(s, L.notice.once(t)), S.among(s, t), Bool.or(S.same(s, h), S.among(s, t)), ih, lnd.once_at(S.same(s, h), s, h, t, {==}, ht))
    case False{}:
      Equal.cong(Bool, Bool, z => Bool.or(S.same(s, h), z), S.among(s, L.notice.once(t)), S.among(s, t), ih)

# a list made once holds the labels it came from
def lnd.once(+s: String, ls: List<&2, String>) -> {S.among(s, L.notice.once(ls)) == S.among(s, ls) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      lnd.once_lbl(L.has(h, t), s, h, t, {==}, lnd.once(s, t))

def Limits.limits_notice_told(ws, r, told, s):
  +line = Nat.sub(1000n, r)
  +ov = L.notice.over(ws, line)
  +kp = L.notice.keep(told, L.notice.labels(ws))
  %Equal.sym(Bool, S.among(s, L.notice.once(List.append(&2, String, ov, kp))), S.among(s, List.append(&2, String, ov, kp)), lnd.once(s, List.append(&2, String, ov, kp))) : {_ == S.told_after(s, ws, line, told) : Bool}
  %Equal.sym(Bool, S.among(s, List.append(&2, String, ov, kp)), Bool.or(S.among(s, ov), S.among(s, kp)), lnd.app(s, ov, kp)) : {_ == S.told_after(s, ws, line, told) : Bool}
  %Equal.sym(Bool, S.among(s, ov), S.reached(s, ws, line), lnd.over(s, ws, line)) : {Bool.or(_, S.among(s, kp)) == S.told_after(s, ws, line, told) : Bool}
  %Equal.sym(Bool, S.among(s, kp), Bool.and(S.among(s, told), Bool.not(S.among(s, L.notice.labels(ws)))), lnd.keep(s, told, L.notice.labels(ws))) : {Bool.or(S.reached(s, ws, line), _) == S.told_after(s, ws, line, told) : Bool}
  %Equal.sym(List<&2, String>, L.notice.labels(ws), S.labels(ws), lnd.lbl(ws)) : {Bool.or(S.reached(s, ws, line), Bool.and(S.among(s, told), Bool.not(S.among(s, _)))) == S.told_after(s, ws, line, told) : Bool}
  %Equal.sym(Bool, S.among(s, S.labels(ws)), Bool.or(S.reached(s, ws, line), S.below(s, ws, line)), lnd.labels(s, ws, line)) : {Bool.or(S.reached(s, ws, line), Bool.and(S.among(s, told), Bool.not(_))) == S.told_after(s, ws, line, told) : Bool}
  lnd.final(S.reached(s, ws, line), S.among(s, told), S.below(s, ws, line))
