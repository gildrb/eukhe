# eukhe: the proof of LAW stop_question_anywhere_stands
#
# PROOF: the fold maps char by char, so the folded reply is the folded
# text before, `?` (folded to itself), then the folded text after
# (sq.fold_append); the question-mark phrase of the ask table, free on
# both edges, is found there (phrase_search_complete), so the spec's ask
# test holds and the asked reply stands (stop_asked_stands).

import Base
import ../../bend/stop.bend as S
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ../../laws/text_pat.bend as TextPat
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop
import ../phrase/phrase_search_complete.bend as PPhraseSearchComplete
import ./stop_asked_stands.bend as PStopAskedStands

# the fold of a then b is the fold of a, then the fold of b
def sq.fold_append(a: String, -b: String) -> {TextPat.sp_fold(String.append(a, b)) == String.append(TextPat.sp_fold(a), TextPat.sp_fold(b)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(String, TextPat.sp_fold(String.append(t, b)), String.append(TextPat.sp_fold(t), TextPat.sp_fold(b)), sq.fold_append(t, b)) : {SCon{Chr{TextPat.sp_fold_code(Char.to_u32(c))}, _} == SCon{Chr{TextPat.sp_fold_code(Char.to_u32(c))}, String.append(TextPat.sp_fold(t), TextPat.sp_fold(b))} : String}
      {==}

# the question mark is found in a folded text that holds it
def sq.found(+fa: String, +fb: String) -> {P.found(String.append(fa, String.append("?", fb)), P.Ph{P.EFree{}, StSpec.chars("?", []), P.EFree{}}) == True{} : Bool}:
  Phrase.phrase_search_complete(fa, "?", fb, P.EFree{}, StSpec.chars("?", []), P.EFree{}, {==}, {==}, {==})

# the spec's ask test holds for a reply with a question mark anywhere
def sq.asks(+a: String, +b: String) -> {StSpec.asks(String.append(a, SCon{'?', b})) == True{} : Bool}:
  +fa = TextPat.sp_fold(a)
  +fb = TextPat.sp_fold(b)
  %Equal.sym(String, TextPat.sp_fold(String.append(a, SCon{'?', b})), String.append(fa, TextPat.sp_fold(SCon{'?', b})), sq.fold_append(a, SCon{'?', b})) : {Phrase.sp_any(_, StSpec.ask_table()) == True{} : Bool}
  %Equal.sym(Bool, P.found(String.append(fa, String.append("?", fb)), P.Ph{P.EFree{}, StSpec.chars("?", []), P.EFree{}}), True{}, sq.found(fa, fb)) : {Bool.or(_, Phrase.sp_any(String.append(fa, String.append("?", fb)), P.Ph{P.EFree{}, StSpec.chars("？", []), P.EFree{}} <> StSpec.word_starts(["let me know", "let us know", "would you like", "do you want", "should i ", "shall i ", "please confirm", "can you confirm", "your call"]))) == True{} : Bool}
  {==}

def Stop.stop_question_anywhere_stands(p, a, b):
  Stop.stop_asked_stands(p, String.append(a, SCon{'?', b}), sq.asks(a, b))
