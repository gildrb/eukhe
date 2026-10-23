# eukhe: lemmas the proofs of two or more areas share: logic

import Base

def pf.snd(-A: Type, -B: Type, p: (A & B)) -> B:
  (a, b) = p
  b
