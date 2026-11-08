# eukhe: the proof of LAW replace_lt_shared_head
#
# PROOF of LAW replace_lt_shared_head: a number compares equal to itself
# (LAReplace.pr.lex_same).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_lt_shared_head(x, xs, ys):
  LAReplace.pr.lex_same(x, Rp.lt(xs, ys))
