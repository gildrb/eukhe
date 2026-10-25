# eukhe: the proof of LAW overflow_message_found
#
# PROOF: the code's message test is the spec's (LA.ovb.message). The
# message is not empty (its fold holds the part u, and u is not), no calm
# pattern is found (the premise), and an overflow pattern is: the part u
# matches its alternative, so the search finds it in a ++ u ++ b
# (text_pat_search_complete), which is the folded message; the table, split
# around that alternative, is then found by its alternative (omf.any_split).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ../text_pat/text_pat_search_complete.bend as PTextPatSearchComplete
import ./base.bend as LA

def omf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def omf.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : omf.BD(_, Unit, A)
  Unit{}

def omf.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# u ++ b is not empty when u is not
def omf.app_ne(u: String, -b: String, hn: {String.is_empty(u) == False{} : Bool}) -> {String.is_empty(String.append(u, b)) == False{} : Bool}:
  match u:
    case SNil{}:
      omf.absurd({String.is_empty(String.append(SNil{}, b)) == False{} : Bool}, hn)
    case SCon{c, t}:
      {==}

# a ++ (u ++ b) is not empty when u is not
def omf.app3_ne(a: String, +u: String, +b: String, hn: {String.is_empty(u) == False{} : Bool}) -> {String.is_empty(String.append(a, String.append(u, b))) == False{} : Bool}:
  match a:
    case SNil{}:
      omf.app_ne(u, b, hn)
    case SCon{c, t}:
      {==}

# a message whose fold is a non-empty text is not empty
def omf.ne(msg: String, +s: String, hf: {TextPat.sp_fold(msg) == s : String}, hs: {String.is_empty(s) == False{} : Bool}) -> {String.is_empty(msg) == False{} : Bool}:
  match msg:
    case SNil{}:
      omf.absurd({String.is_empty(SNil{}) == False{} : Bool}, Equal.trans(Bool, True{}, String.is_empty(s), False{}, Equal.cong(String, Bool, String.is_empty, SNil{}, s, hf), hs))
    case SCon{c, t}:
      {==}

# an alternative found makes its list of alternatives found
def omf.alts_split(apre: List<&2, List<&2, Tp.It>>, +s: String, +its: List<&2, Tp.It>, +apost: List<&2, List<&2, Tp.It>>, +h: {Tp.occ(s, its) == True{} : Bool}) -> {TextPat.sp_alts(False{}, s, List.append(&2, List<&2, Tp.It>, apre, its <> apost)) == True{} : Bool}:
  match apre:
    case Nil{}:
      %Equal.sym(Bool, Tp.occ(s, its), True{}, h) : {Bool.or(_, TextPat.sp_alts(False{}, s, apost)) == True{} : Bool}
      {==}
    case x <> more:
      %Equal.sym(Bool, TextPat.sp_alts(False{}, s, List.append(&2, List<&2, Tp.It>, more, its <> apost)), True{}, omf.alts_split(more, s, its, apost, h)) : {Bool.or(TextPat.sp_found(False{}, s, x), _) == True{} : Bool}
      omf.or_true(TextPat.sp_found(False{}, s, x))

# an unanchored pattern whose alternative is found makes the table found
def omf.any_split(pre: List<&2, Tp.Pat>, +s: String, +apre: List<&2, List<&2, Tp.It>>, +its: List<&2, Tp.It>, +apost: List<&2, List<&2, Tp.It>>, +post: List<&2, Tp.Pat>, +h: {Tp.occ(s, its) == True{} : Bool}) -> {TextPat.sp_any(s, List.append(&2, Tp.Pat, pre, Tp.Pat{False{}, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, TextPat.sp_alts(False{}, s, List.append(&2, List<&2, Tp.It>, apre, its <> apost)), True{}, omf.alts_split(apre, s, its, apost, h)) : {Bool.or(_, TextPat.sp_any(s, post)) == True{} : Bool}
      {==}
    case p <> more:
      match p:
        case Tp.Pat{x, alts}:
          %Equal.sym(Bool, TextPat.sp_any(s, List.append(&2, Tp.Pat, more, Tp.Pat{False{}, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post)), True{}, omf.any_split(more, s, apre, its, apost, post, h)) : {Bool.or(TextPat.sp_alts(x, s, alts), _) == True{} : Bool}
          omf.or_true(TextPat.sp_alts(x, s, alts))

# the message test's shape: not empty, nothing calm, an overflow found
def omf.pick(e: Bool, -c: Bool, -o: Bool, -w: Bool, he: {e == False{} : Bool}, hc: {c == False{} : Bool}, ho: {o == True{} : Bool}) -> {Bool.and(Bool.not(e), Bool.and(Bool.not(c), Bool.or(o, w))) == True{} : Bool}:
  match e:
    case True{}:
      omf.absurd({Bool.and(Bool.not(True{}), Bool.and(Bool.not(c), Bool.or(o, w))) == True{} : Bool}, he)
    case False{}:
      %Equal.sym(Bool, c, False{}, hc) : {Bool.and(Bool.not(_), Bool.or(o, w)) == True{} : Bool}
      %Equal.sym(Bool, o, True{}, ho) : {Bool.or(_, w) == True{} : Bool}
      {==}

# the folded message holds the part: the search finds it
def omf.occ(+msg: String, +a: String, +u: String, +b: String, +its: List<&2, Tp.It>, hf: {TextPat.sp_fold(msg) == String.append(a, String.append(u, b)) : String}, hu: {TextPat.sp_lang(u, its) == True{} : Bool}) -> {Tp.occ(TextPat.sp_fold(msg), its) == True{} : Bool}:
  %Equal.sym(String, TextPat.sp_fold(msg), String.append(a, String.append(u, b)), hf) : {Tp.occ(_, its) == True{} : Bool}
  TextPat.text_pat_search_complete(a, u, b, its, hu)

# the overflow table, split around the alternative, is found
def omf.hit(+f: String, +pre: List<&2, Tp.Pat>, +apre: List<&2, List<&2, Tp.It>>, +its: List<&2, Tp.It>, +apost: List<&2, List<&2, Tp.It>>, +post: List<&2, Tp.Pat>, hp: {Overflow.sp_overflow_pats() == List.append(&2, Tp.Pat, pre, Tp.Pat{False{}, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post) : List<&2, Tp.Pat>}, h: {Tp.occ(f, its) == True{} : Bool}) -> {TextPat.sp_any(f, Overflow.sp_overflow_pats()) == True{} : Bool}:
  %Equal.sym(List<&2, Tp.Pat>, Overflow.sp_overflow_pats(), List.append(&2, Tp.Pat, pre, Tp.Pat{False{}, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post), hp) : {TextPat.sp_any(f, _) == True{} : Bool}
  omf.any_split(pre, f, apre, its, apost, post, h)

def Overflow.overflow_message_found(msg, provider, a, u, b, pre, apre, its, apost, post, hp, hf, hu, hn, hc):
  +f = TextPat.sp_fold(msg)
  %Equal.sym(Bool, O.message_overflow(msg, provider), Overflow.sp_message(msg, provider), LA.ovb.message(msg, provider)) : {_ == True{} : Bool}
  omf.pick(String.is_empty(msg), TextPat.sp_any(f, Overflow.sp_calm_pats()), TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(provider, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()])), omf.ne(msg, String.append(a, String.append(u, b)), hf, omf.app3_ne(a, u, b, hn)), hc, omf.hit(f, pre, apre, its, apost, post, hp, omf.occ(msg, a, u, b, its, hf, hu)))
