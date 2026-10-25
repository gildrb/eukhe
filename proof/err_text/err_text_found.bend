# eukhe: the proof of LAW err_text_found
#
# PROOF: the folded text is a ++ u ++ b, so the phrase is found in it
# (phrase_search_complete); the table, split around that phrase, is then
# found (LA.etb.any_split), so the text holds, and so does the list split
# around the text (LA.etb.list_split); the code's answer is the spec's
# (err_text_decides).

import Base
import ../../bend/phrase.bend as P
import ../../bend/err_text.bend as E
import ../../laws/text_pat.bend as TextPat
import ../../laws/phrase.bend as Phrase
import ../../laws/err_text.bend as ErrText
import ../phrase/phrase_search_complete.bend as PPhraseSearchComplete
import ./err_text_decides.bend as PErrTextDecides
import ./base.bend as LA

# the phrase is found in the folded text
def etf.found(+text: String, +a: String, +u: String, +b: String, +st: P.Edge, +its: List<&2, P.It>, +en: P.Edge, hf: {TextPat.sp_fold(text) == String.append(a, String.append(u, b)) : String}, hu: {Phrase.sp_lang(u, its) == True{} : Bool}, hs: {Phrase.sp_start_ok(st, a) == True{} : Bool}, he: {Phrase.sp_end_ok(en, b) == True{} : Bool}) -> {P.found(TextPat.sp_fold(text), P.Ph{st, its, en}) == True{} : Bool}:
  %Equal.sym(String, TextPat.sp_fold(text), String.append(a, String.append(u, b)), hf) : {P.found(_, P.Ph{st, its, en}) == True{} : Bool}
  Phrase.phrase_search_complete(a, u, b, st, its, en, hu, hs, he)

# the text holds for the rule
def etf.text(+r: E.Rule, +text: String, +pre: List<&2, P.Ph>, +ph: P.Ph, +post: List<&2, P.Ph>, hp: {ErrText.sp_table(r) == List.append(&2, P.Ph, pre, ph <> post) : List<&2, P.Ph>}, h: {P.found(TextPat.sp_fold(text), ph) == True{} : Bool}) -> {ErrText.sp_holds_text(r, text) == True{} : Bool}:
  %Equal.sym(List<&2, P.Ph>, ErrText.sp_table(r), List.append(&2, P.Ph, pre, ph <> post), hp) : {Phrase.sp_any(TextPat.sp_fold(text), _) == True{} : Bool}
  LA.etb.any_split(pre, TextPat.sp_fold(text), ph, post, h)

def ErrText.err_text_found(r, tp, text, tq, a, u, b, pre, st, its, en, post, hp, hf, hu, hs, he):
  +ts = List.append(&2, String, tp, text <> tq)
  +h1 = etf.found(text, a, u, b, st, its, en, hf, hu, hs, he)
  +h2 = etf.text(r, text, pre, P.Ph{st, its, en}, post, hp, h1)
  %Equal.sym(Bool, E.holds(r, ts), ErrText.sp_holds(r, ts), ErrText.err_text_decides(r, ts)) : {_ == True{} : Bool}
  LA.etb.list_split(tp, r, text, tq, h2)
