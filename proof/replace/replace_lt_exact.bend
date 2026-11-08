# eukhe: the proof of LAW replace_lt_exact
# The order lemma of the area (rk.lt_spec: by induction on both ranks, each
# step the lexicographic test of the heads).

import Base
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_lt_exact(xs, ys):
  LAReplace.rk.lt_spec(xs, ys)
