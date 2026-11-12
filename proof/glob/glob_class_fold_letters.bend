# eukhe: the proof of LAW glob_class_fold_letters
#
# PROOF: both sides compute equal per letter pair: the code's other case of
# each literal letter computes to the pair's other letter.

import Base
import ../../laws/glob.bend as Glob

def Glob.glob_class_fold_letters(rs):
  {==}
