# eukhe: the proof of LAW limits_prefix_untouched
#
# PROOF: the code's first word is the spec's lead (lpu.lead), read folded
# and compared as the spec does (limits_prefix_reads' lpr.folded,
# LB.lmb.same): that is opens, which is False, so the message is the rest.

import Base
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ./limits_prefix_reads.bend as PPrefixReads

def lpu.after.at(sp: Bool, c: Char, t: String, after: String) -> String:
  match sp:
    case True{}:
      SCon{c, t}
    case False{}:
      after

# the text of s from its first space on
def lpu.after(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      lpu.after.at(S.space(c), c, t, lpu.after(t))

def lpu.lead_at(b: Bool, c: Char, t: String, x: String, y: String) -> {L.word.at(b, c, t, L.Cut{x, y}) == L.Cut{S.lead.at(b, c, x), lpu.after.at(b, c, t, y)} : L.Cut}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's first word is the spec's lead
def lpu.lead(s: String) -> {L.word(s) == L.Cut{S.lead(s), lpu.after(s)} : L.Cut}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, L.is_space(c), S.space(c), PPrefixReads.lpr.space(c)) : {L.word.at(_, c, t, L.word(t)) == L.Cut{S.lead.at(S.space(c), c, S.lead(t)), lpu.after.at(S.space(c), c, t, lpu.after(t))} : L.Cut}
      %Equal.sym(L.Cut, L.word(t), L.Cut{S.lead(t), lpu.after(t)}, lpu.lead(t)) : {L.word.at(S.space(c), c, t, _) == L.Cut{S.lead.at(S.space(c), c, S.lead(t)), lpu.after.at(S.space(c), c, t, lpu.after(t))} : L.Cut}
      lpu.lead_at(S.space(c), c, t, S.lead(t), lpu.after(t))

def Limits.limits_prefix_untouched(s, ns, h):
  %Equal.sym(L.Cut, L.word(s), L.Cut{S.lead(s), lpu.after(s)}, lpu.lead(s)) : {L.prefix.word(_, ns, s) == L.Read{Nil{}, Nil{}, s} : L.Prefix}
  %Equal.sym(String, L.folded(S.lead(s)), S.folded(S.lead(s)), PPrefixReads.lpr.folded(S.lead(s))) : {L.prefix.at(L.same(_, "/b"), lpu.after(s), ns, s) == L.Read{Nil{}, Nil{}, s} : L.Prefix}
  %Equal.sym(Bool, L.same(S.folded(S.lead(s)), "/b"), S.opens(s), LB.lmb.same(S.folded(S.lead(s)), "/b")) : {L.prefix.at(_, lpu.after(s), ns, s) == L.Read{Nil{}, Nil{}, s} : L.Prefix}
  %Equal.sym(Bool, S.opens(s), False{}, h) : {L.prefix.at(_, lpu.after(s), ns, s) == L.Read{Nil{}, Nil{}, s} : L.Prefix}
  {==}
