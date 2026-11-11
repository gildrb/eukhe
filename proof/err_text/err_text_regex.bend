# eukhe: the proof of LAW err_text_regex
#
# PROOF: by induction on the texts; per text the fold is the spec's
# (text_pat_fold), the table found where the regex's phrases are (LA.etb.same)
# and the search the spec's (phrase_any); the lazy or is the Bool or
# (LA.etb.holds).

import Base
import ../../bend/err_text.bend as E
import ../../laws/err_text.bend as ErrText
import ./base.bend as LA

def ErrText.err_text_regex(r, texts):
  LA.etb.holds(r, texts)
