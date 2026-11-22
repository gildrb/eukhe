# eukhe: the proof of LAW theme_missing_absent: the lemma the reader's
# proofs share, by induction over the tokens (base.bend pt.missing_absent)

import Base
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_missing_absent(cols):
  LA.pt.missing_absent(cols)
