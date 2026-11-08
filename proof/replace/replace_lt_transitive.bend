# eukhe: the proof of LAW replace_lt_transitive
#
# PROOF of LAW replace_lt_transitive: by induction on the three ranks,
# each step the order of the first numbers (LAReplace.pr.lt_trans).

import Base
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_lt_transitive(xs, ys, zs, below, then):
  LAReplace.pr.lt_trans(xs, ys, zs, below, then)
