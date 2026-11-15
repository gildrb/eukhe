# eukhe: the proof of LAW limits_notice_told_once
#
# PROOF: the labels told of after are a list with each label once
# (notice.once): a label is kept only when the rest has no label of its
# text, and the rest holds the same labels as the list it came from
# (lto.once, on lnd.once and lnt.has).

import Base
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./limits_notice_tells.bend as PNoticeTells
import ./limits_notice_told.bend as PNoticeTold

# a label kept before the rest made once
def lto.once_lbl(b: Bool, +h: String, +t: List<&2, String>, eb: {L.has(h, t) == b : Bool}, ih: {Limits.sp_distinct(L.notice.once(t)) == True{} : Bool}) -> {Limits.sp_distinct(L.notice.label(Bool.not(b), h, L.notice.once(t))) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      +eh = Equal.trans(Bool, S.among(h, t), L.has(h, t), False{}, Equal.sym(Bool, L.has(h, t), S.among(h, t), PNoticeTells.lnt.has(h, t)), eb)
      +e1 = Equal.trans(Bool, S.among(h, L.notice.once(t)), S.among(h, t), False{}, PNoticeTold.lnd.once(h, t), eh)
      %Equal.sym(Bool, S.among(h, L.notice.once(t)), False{}, e1) : {Bool.and(Bool.not(_), Limits.sp_distinct(L.notice.once(t))) == True{} : Bool}
      ih

# a list made once holds no label twice
def lto.once(ls: List<&2, String>) -> {Limits.sp_distinct(L.notice.once(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      lto.once_lbl(L.has(h, t), h, t, {==}, lto.once(t))

def Limits.limits_notice_told_once(ws, r, told, dw, dt):
  lto.once(List.append(&2, String, L.notice.over(ws, Nat.sub(1000n, r)), L.notice.keep(told, L.notice.labels(ws))))
